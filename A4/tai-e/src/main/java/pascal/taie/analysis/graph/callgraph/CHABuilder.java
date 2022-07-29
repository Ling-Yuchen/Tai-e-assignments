/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.offer(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.poll();
            if (!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                for (Stmt stmt : method.getIR().getStmts()) {
                    if (stmt instanceof Invoke callSite) {
                        for (JMethod target : resolve(callSite)) {
                            CallKind callKind;
                            if (callSite.isStatic()) { callKind = CallKind.STATIC; }
                            else if (callSite.isSpecial()) { callKind = CallKind.SPECIAL; }
                            else if (callSite.isInterface()) { callKind = CallKind.INTERFACE; }
                            else if (callSite.isVirtual()) { callKind = CallKind.VIRTUAL; }
                            else if (callSite.isDynamic()) { callKind = CallKind.DYNAMIC; }
                            else { callKind = CallKind.OTHER; }
                            callGraph.addEdge(new Edge<>(callKind, callSite, target));
                            workList.offer(target);
                        }
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> targets = new HashSet<>();
        JClass classType = callSite.getMethodRef().getDeclaringClass();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();

        if (callSite.isStatic()) {
//            JMethod targetMethod = hierarchy.resolveMethod(callSite.getMethodRef());
            JClass clazz = callSite.getMethodRef().getDeclaringClass();
            Subsignature subSig = callSite.getMethodRef().getSubsignature();
            JMethod targetMethod = clazz.getDeclaredMethod(subSig);
            if (targetMethod != null) { targets.add(targetMethod); }

        } else if (callSite.isSpecial()) {
            JMethod targetMethod = dispatch(classType, subsignature);
            if (targetMethod != null) { targets.add(targetMethod); }

        } else if (callSite.isVirtual()) {
            Queue<JClass> subClasses = new ArrayDeque<>();
            subClasses.add(classType);
            while (!subClasses.isEmpty()) {
                JClass clazz = subClasses.poll();
                JMethod targetMethod = dispatch(clazz, subsignature);
                if (targetMethod != null) { targets.add(targetMethod); }
                subClasses.addAll(hierarchy.getDirectSubclassesOf(clazz));
            }
        } else if (callSite.isInterface()) {
            // if the call kind is INTERFACE, we should search:
            //     1. all the classes that implements the declared interface
            //     2. all the classes that implements any sub-interface of the declared interface
            // so, we need 2 loops:
            //     the outer loop get all the interfaces
            //     the inner loop get all the classes for each interface
            Queue<JClass> subInterfaces = new ArrayDeque<>();
            subInterfaces.add(classType);
            while (!subInterfaces.isEmpty()) {
                JClass interfaceClass = subInterfaces.poll();
                Queue<JClass> implClasses = new ArrayDeque<>(hierarchy.getDirectImplementorsOf(interfaceClass));
                while (!implClasses.isEmpty()) {
                    JClass clazz = implClasses.poll();
                    JMethod targetMethod = dispatch(clazz, subsignature);
                    if (targetMethod != null) { targets.add(targetMethod); }
                    implClasses.addAll(hierarchy.getDirectSubclassesOf(clazz));
                }
                subInterfaces.addAll(hierarchy.getDirectSubinterfacesOf(interfaceClass));
            }
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JClass clazz = jclass;
        JMethod targetMethod;
        while (clazz != null) {
            targetMethod = clazz.getDeclaredMethod(subsignature);
            if (targetMethod != null &&
                    !targetMethod.isAbstract()) { // the result cannot be abstract
                return targetMethod;
            }
            clazz = clazz.getSuperClass();
        }
        return null;
    }
}
