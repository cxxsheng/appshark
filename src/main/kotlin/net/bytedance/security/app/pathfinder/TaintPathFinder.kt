/*
* Copyright 2022 Beijing Zitiao Network Technology Co., Ltd.
*
* Licensed under the Apache License, Version 2.0 (the "License");
* you may not use this file except in compliance with the License.
* You may obtain a copy of the License at
*
*     http://www.apache.org/licenses/LICENSE-2.0
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific language governing permissions and
* limitations under the License.
*/


package net.bytedance.security.app.pathfinder

import net.bytedance.security.app.Log
import net.bytedance.security.app.PLUtils
import net.bytedance.security.app.PreAnalyzeContext
import net.bytedance.security.app.getConfig
import net.bytedance.security.app.pointer.PLLocalPointer
import net.bytedance.security.app.pointer.PLPointer
import net.bytedance.security.app.pointer.PLPtrObjectField
import net.bytedance.security.app.result.OutputSecResults
import net.bytedance.security.app.ruleprocessor.ConstModeProcessor
import net.bytedance.security.app.rules.ConstNumberModeRule
import net.bytedance.security.app.rules.ConstStringModeRule
import net.bytedance.security.app.rules.TaintFlowRule
import net.bytedance.security.app.sanitizer.SanitizeContext
import net.bytedance.security.app.sanitizer.SanitizerFactory
import net.bytedance.security.app.taintflow.AnalyzeContext
import net.bytedance.security.app.taintflow.AnalyzeContext.Companion.isPrimePtr
import net.bytedance.security.app.taintflow.TaintAnalyzer
import net.bytedance.security.app.taintflow.TwoStagePointerAnalyze
import net.bytedance.security.app.ui.TaintPathModeHtmlWriter
import net.bytedance.security.app.util.toFormatedString
import net.bytedance.security.app.util.toSortedMap
import net.bytedance.security.app.util.toSortedSet
import soot.jimple.IntConstant
import soot.jimple.LongConstant
import soot.jimple.NumericConstant
import soot.jimple.StringConstant
import java.util.*

/**
 * After pointer analyze, find the shortest path from source to sink,
 * and then generate the final vulnerability report
 */
class TaintPathFinder(
    val ctx: PreAnalyzeContext,
    private val analyzeContext: AnalyzeContext,
    val rule: TaintFlowRule,
    val analyzer: TaintAnalyzer,
) {
    //todo Remember that PLPointer in Analyzer and Sanitizer are different from PLPointer in PointFactory
    suspend fun findPath() {
        Log.logDebug(String.format("start analyze pointers %s", rule.name))
        if (rule is ConstStringModeRule || rule is ConstNumberModeRule) {
            findConstPath()
        } else {
            findTaintPath()
        }
    }

    /**
     *ConstNumberMode and ConstStringMode  don't support sanitizer
     */
    private suspend fun findConstPath() {
        runConstAnalyze(analyzer)
    }

    private suspend fun findTaintPath() {
        runTaintAnalyze(analyzer)
    }

    /**
     * find the path from the const string or number to the sink,
     * 1. find all pointers can flow to sink
     * 2. filter these pointers if they are const string or number
     * 3. write the path from  each const to the sink to the result
     * */
    private suspend fun runConstAnalyze(analyzer: TaintAnalyzer) {
        for (ptr in analyzer.sinkPtrSet) {
            val sinkTaintedSet = analyzeContext.collectReversePropagation(ptr, rule.primTypeAsTaint)
            if (sinkTaintedSet.isEmpty()) {
                Log.logDebug("nodes empty $ptr")
                continue
            }
            val strSet: MutableSet<PLLocalPointer> = HashSet()
            val numSet: MutableSet<Pair<PLLocalPointer, Long>> = HashSet()
            for (ptrLocal in sinkTaintedSet) {
                if (ptrLocal !is PLLocalPointer || ptrLocal.constant == null) {
                    continue
                }
                val constant = ptrLocal.constant
                if (constant is StringConstant) {
                    strSet.add(ptrLocal)
                } else if (constant is NumericConstant) {
                    if (constant is IntConstant) {
                        numSet.add(Pair(ptrLocal, constant.value.toLong()))
                    } else if (constant is LongConstant) {
                        numSet.add(Pair(ptrLocal, constant.value))
                    }
                }
            }
            if (rule is ConstStringModeRule) {
                for (constStr in strSet) {
                    Log.logDebug("const str $constStr")
                    findConstStringPath(
                        constStr,
                        analyzer.sinkPtrSet
                    )
                }
            } else if (rule is ConstNumberModeRule) {
                for (num in numSet) {
                    Log.logDebug("const num $num")
                    findConstNumberPath(
                        num,
                        analyzer.sinkPtrSet
                    )
                }
            }
        }
    }

    /**
     * if the src satisfy the constraints ,then find the shortest path.
     * exists of the path is verified
     */
    private suspend fun findConstNumberPath(
        src: Pair<PLLocalPointer, Long>,
        sinkPtrSet: Set<PLLocalPointer>,
    ) {
        val isMatch = isConstNumRuleMatch(src.second)
        if (!isMatch) {
            return
        }
        findConstPath(src.first, sinkPtrSet)
        return
    }

    /**
     * constraints for ConstNumberMode
     */
    private fun isConstNumRuleMatch(constNumber: Long): Boolean {
        assert(rule is ConstNumberModeRule)
        val constNumberModeRule = rule as ConstNumberModeRule
        if (constNumberModeRule.targetNumberArr == null) {
            return true
        }
        if (constNumberModeRule.targetNumberArr.contains(constNumber.toInt())) {
            return true
        }
        return false
    }

    /**
     * constraints for ConstStringMode
     */
    private fun isConstStringRuleMatch(constStr: String): Boolean {
        var isMatch = false
        if (rule !is ConstStringModeRule) {
            return false
        }
        if (rule.constLen != null) {
            val constStrLen = constStr.length
            if (constStrLen > 0 && constStrLen % rule.constLen == 0) {
                if (rule.targetStringArr != null) {
                    if (ConstModeProcessor.isMatchTargetConstStr(constStr, rule.targetStringArr)) {
                        isMatch = true
                    }
                } else {
                    isMatch = true
                }
            }
        } else {
            if (rule.targetStringArr != null) {
                if (ConstModeProcessor.isMatchTargetConstStr(constStr, rule.targetStringArr)) {
                    isMatch = true
                }
            } else if (rule.minLen != null) {
                if (constStr.length >= rule.minLen) {
                    isMatch = true
                }
            } else {
                isMatch = true
            }
        }
        return isMatch
    }


    private suspend fun findConstPath(
        srcPtr: PLLocalPointer,
        sinkPtrSet: Set<PLLocalPointer>,
    ) {
        calcPath(srcPtr, sinkPtrSet, false)
    }

    /**
     * if the src satisfy the constraints ,then find the shortest path.
     * exists of the path is verified
     */
    private suspend fun findConstStringPath(
        srcPtr: PLLocalPointer,
        sinkPtrSet: Set<PLLocalPointer>
    ) {
        val constStr = srcPtr.variableName
        val isMatch = isConstStringRuleMatch(constStr)
        if (!isMatch) {
            return
        }
        findConstPath(srcPtr, sinkPtrSet)
        return
    }

    private suspend fun runTaintAnalyze(analyzer: TaintAnalyzer) {
        calcPathFromSourceTaint(
            analyzer.sourcePtrSet,
            analyzer.sinkPtrSet,
            analyzer.mustPassedPtrSet,
        )

    }

    /**
     *  filter by sanitizer then find the shortest path.
     * @param sourcePtrSet
     * @param sinkPtrSet
     * todo use multi threads to search
     */
    private suspend fun calcPathFromSourceTaint(
        sourcePtrSet: Set<PLLocalPointer>,
        sinkPtrSet: Set<PLLocalPointer>,
        mustPassedPtrSet : Set<PLLocalPointer>?,
    ) {
        for (sourcePtr in sourcePtrSet) {
            if (checkSanitizeRules(sourcePtr)) {
                Log.logDebug("Sanitize Check Pass")
                continue
            }
            Log.logDebug("======> ParamSources Calculate realizable path from $sourcePtr")
            TwoStagePointerAnalyze.recordMethodTakesTime(
                "calcPathFromSourceTaint ${this.analyzer.entryMethod.signature}-${sourcePtr.signature()}",
                3000
            ) {

                //查看是否需要进行第一步路径计算，mustPassedPtrSet为null说明规则为空
                var shouldPass = true
                mustPassedPtrSet?.let {
                    shouldPass = calcPath(
                        sourcePtr,
                        mustPassedPtrSet,
                        true
                    )

                    if (shouldPass)
                        Log.logInfo("Found mustPassedPtrSet $it, start second round calcPath")
                    else
                        Log.logInfo("Cannot Find mustPassedPtrSet $it, end calcPath")

                }
                if (shouldPass){
                    calcPath(sourcePtr, sinkPtrSet, false)
                }
            }

        }
    }

    private fun isThisSolverNeedLog(): Boolean {
        return this.rule.isThisRuleNeedLog()
    }

    /**
     * Try to find the shortest path from srcPtr to sinkPtrSet
     * return true if found Path
     */
    private suspend fun calcPath(
        srcPtr: PLPointer,
        sinkPtrSet: Set<PLLocalPointer>,
        isInternalUse: Boolean
    ): Boolean {
        if (isThisSolverNeedLog()) {
            val sb = StringBuilder()
            val sinkTaintedSet = HashSet<PLPointer>()
            for (sink in sinkPtrSet) {
                sinkTaintedSet.addAll(analyzeContext.collectReversePropagation(sink, rule.primTypeAsTaint))
            }
            sb.append("sinkPtrSet=${sinkPtrSet.toSortedSet()}, taint sinkNodeSet: ${sinkTaintedSet.toSortedSet()}\n")
            PLUtils.writeFile(getConfig().outPath + "/sink.log", sb.toString())
            sb.clear()
            sb.append("\n\n\n\n\n\nsrcPtr=${srcPtr}, taint sourceNodeSet:\n")
            val srcTaintedSet = analyzeContext.collectPropagation(srcPtr, rule.primTypeAsTaint)
            sb.append("\n\nsrcTaintedSet=${srcTaintedSet.toSortedSet()}")
            PLUtils.writeFile(getConfig().outPath + "/source.log", sb.toString())
            sb.clear()
            PLUtils.writeFile(
                getConfig().outPath + "/ptrToSet.log",
                analyzeContext.pointerToObjectSet.toSortedMap().toFormatedString()
            )
            PLUtils.writeFile(
                getConfig().outPath + "/taintPtrFlowGraph.log",
                analyzeContext.variableFlowGraph.toSortedMap().toFormatedString()
            )
            PLUtils.writeFile(
                getConfig().outPath + "/ptrFlowGraph.log",
                analyzeContext.pointerFlowGraph.toSortedMap().toFormatedString()
            )
            PLUtils.writeFile(getConfig().outPath + "rm.log", analyzeContext.rm.toSortedSet().toFormatedString())
//            exitProcess(3)
        }
        val g = analyzeContext.variableFlowGraph

        // 对于src应该指向的不仅仅是@this，还应该指向@this.data
        // fixme 是否需要做类型检查呢吗 用于针对intent的测试
        if (rule.PreciseTaint) {
            // 从 entry 进来的还需要进行this.data的 taint
            val fields = analyzeContext.findObjectFieldsByPointer(srcPtr)
//            if (fields.isNotEmpty())
//                println("hello ${srcPtr} -->> {${fields.toSortedSet()}")
            for (field in fields) {
                var sets = g[srcPtr]
                if (sets == null) {
                    sets = HashSet()
                    g[srcPtr] = sets
                }
                if (!sets.contains(field))
                    sets.add(field)
            }

        }
        val path = bfsSearch(srcPtr, sinkPtrSet, g, getConfig().maxPathLength, rule.name, rule.primTypeAsTaint) ?: return false
        if (!isInternalUse) {
            val result = PathResult(path)
            try {
                TaintPathModeHtmlWriter(
                    OutputSecResults,
                    analyzer,
                    result,
                    rule
                ).addVulnerabilityAndSaveResultToOutput()
            } catch (ex: Exception) {
                ex.printStackTrace()
            }
        }
        return true
    }


    /**
     *  entry point of  the sanitizer
     */
    private fun checkSanitizeRules(sourcePtr: PLLocalPointer): Boolean {
        val sanitizeContext = SanitizeContext(analyzeContext, sourcePtr)
        SanitizerFactory.createSanitizers(rule, ctx).forEach {
            if (it.matched(sanitizeContext)) {
                return true
            }
        }
        return false
    }


    companion object {
        data class PointerAndDepth(val p: PLPointer, val depth: Int)

        /**
         * breath first search for the shortest path
         * @param sourcePointer source
         * @param destinations possible destinations
         * @param g graph
         * @param maxPath the maximum size of the shortest path
         * @param name for log
         * @param isIncludePrimeTaint whether prime type should be considered in the Taint
         * @return the shortest path from src to dst or null if no path found
         */
        fun bfsSearch(
            sourcePointer: PLPointer,
            destinations: Set<PLPointer>,
            g: Map<PLPointer, Set<PLPointer>>,
            maxPath: Int,
            name: String,
            isIncludePrimeTaint: Boolean = true,
        ): List<PLPointer>? {
            val parents = HashMap<PLPointer, PLPointer>()
            val queue = LinkedList<PointerAndDepth>()
            val visited = HashSet<PLPointer>()
            queue.addLast(PointerAndDepth(sourcePointer, 0))
            var validDst: PLPointer? = null
            visited.add(sourcePointer)
            found@ while (queue.isNotEmpty()) {
                val src = queue.pollFirst()
                if (destinations.contains(src.p)) {
                    validDst = src.p
                    break@found
                }

                if (src.depth >= maxPath) {
                    break //The path length exceeded the upper limit
                }
                val next = g[src.p] ?: continue

                for (n in next) {
                    if (visited.contains(n)) {
                        continue
                    }

                    if(!isIncludePrimeTaint && isPrimePtr(n))
                        continue

                    visited.add(n)
                    parents[n] = src.p
                    queue.addLast(PointerAndDepth(n, src.depth + 1))
                }
            }
            if (validDst == null) {
                return null
            }

            val path = ArrayList<PLPointer>()
            var n = validDst
            while (n != null) {
                path.add(n)
                n = parents[n]
            }
            if (path.size >= maxPath) {
                Log.logWarn("path too long: for $name is discarded,currentLen=${path.size},maxLen=$maxPath")
                return null
            }
            return path.reversed()
        }


    }
}