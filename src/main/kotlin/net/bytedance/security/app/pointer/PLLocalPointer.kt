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


package net.bytedance.security.app.pointer

import net.bytedance.security.app.PLUtils
import net.bytedance.security.app.util.profiler
import soot.SootField
import soot.SootMethod
import soot.Type
import soot.jimple.ClassConstant
import soot.jimple.Constant

/**
 * to save memory
 */
const val shortNameEnable = false


/**
 * Pointer to variables and constants generated during analysis
 */
class PLLocalPointer : PLPointer {
    var method: SootMethod
    var variable: String
    var id: String

    override val ptrType: Type
    var constant: Constant? = null
    fun setConst(constant: Constant?) {
        this.constant = constant
    }

    constructor(method: SootMethod, localName: String, origType: Type, sig: String) {
        this.method = method
        variable = localName

        ptrType = PointerFactory.typeWrapper(origType)

        id = sig
        profiler.newPtrLocal(id)
    }

    constructor(method: SootMethod, localName: String, origType: Type) {
        this.method = method
        variable = localName
        // We have a rule that all arrays are converted to 1-dimensional arrays.
        ptrType = PointerFactory.typeWrapper(origType)
        id = getPointerLocalSignature(method, localName)
        profiler.newPtrLocal(id)
    }

    val isParam: Boolean
        get() = variable.startsWith(PLUtils.PARAM)

    val isConstStr: Boolean
        get() = variable.startsWith(PLUtils.CONST_STR)

    val isConst: Boolean
        get() = constant != null

    val isThis: Boolean
        get() = variable == PLUtils.THIS_FIELD
    val isLocal: Boolean
        get() = !isParam && !isThis

    /**
     * name of this variable,for example r0,$r0,
     * if PLPtrLocal is a constant,then it's the value of the constant
     */
    val variableName: String
        get() {
            if (!isConstStr) {
                return variable
            }
            return variable.slice(PLUtils.CONST_STR.length until variable.length)
        }

    override fun toString(): String {
        return this.signature()
    }

    fun constBeautifulString(): String? {
        if (isConst) {
            when (constant) {
                is ClassConstant -> {
                    return convertDescriptorToPath((constant as ClassConstant).value.toString())
                }


            }
        }
        return null
    }

    override fun equals(other: Any?): Boolean {
        return if (other is PLLocalPointer) {
            id == other.id
        } else false
    }

    override fun hashCode(): Int {
        return id.hashCode()
    }

    override fun signature(): String {
        return getLocalLongSignature(method, variable)
    }

    companion object {
        fun getLocalLongSignature(method: SootMethod, localName: String): String {
            return "${method.signature}->$localName"
        }

        fun getPointerLocalSignature(method: SootMethod, localName: String): String {
            if (shortNameEnable) {
                return "${method.shortSignature()}->$localName"
            }
            return getLocalLongSignature(method, localName)
        }

        fun convertDescriptorToPath(descriptor: String): String {
            // 检查是否符合 Lpackage/classname; 格式
            if (descriptor.startsWith("L") && descriptor.endsWith(";")) {
                // 去掉首尾的 "L" 和 ";"
                return descriptor.substring(1, descriptor.length - 1).replace('/','.')
            }
            // 如果格式不符合，直接返回原始字符串
            return descriptor
        }
    }
}

fun SootMethod.shortSignature(): String {
    if (shortNameEnable) {
        return "${this.declaringClass.shortName}:${this.name}"
    }
    return this.signature
}

fun SootField.shortSignature(): String {
    if (shortNameEnable) {
        return "${this.declaringClass.shortName}:${this.name}"
    }
    return this.signature
}

fun Type.shortName(): String {
    if (shortNameEnable) {
        return this.toString().split(".").last()
    }
    return this.toString()
}

