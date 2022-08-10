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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                if (stmt instanceof New ||
                        stmt instanceof Copy ||
                        stmt instanceof StoreField store && store.isStatic() ||
                        stmt instanceof LoadField load && load.isStatic() ||
                        stmt instanceof Invoke invoke && invoke.isStatic()) {
                    stmt.accept(new StmtProcessor(csMethod));
                }
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            CSVar pointer = csManager.getCSVar(context, stmt.getLValue());
            Context objContext = contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt));
            CSObj csObj = csManager.getCSObj(objContext, heapModel.getObj(stmt));
            PointsToSet flowedInObjs = PointsToSetFactory.make(csObj);
            workList.addEntry(pointer, flowedInObjs);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar sourcePtr = csManager.getCSVar(context, stmt.getRValue());
            CSVar targetPtr = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(sourcePtr, targetPtr);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod staticMethod = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(csCallSite, staticMethod);
                CSMethod csMethod = csManager.getCSMethod(calleeContext, staticMethod);

                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csMethod))) {
                    handleNewReachableMethod(csMethod, csCallSite);
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField staticField = stmt.getFieldRef().resolve();
                StaticField sourcePtr = csManager.getStaticField(staticField);
                CSVar targetPtr = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(sourcePtr, targetPtr);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField staticField = stmt.getFieldRef().resolve();
                StaticField targetPtr = csManager.getStaticField(staticField);
                CSVar sourcePtr = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(sourcePtr, targetPtr);
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet setFromSource = source.getPointsToSet();
            if (!setFromSource.isEmpty()) {
                workList.addEntry(target, setFromSource);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, pts);
            if (pointer instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                for (CSObj csObj : delta) {
                    for (StoreField store : var.getStoreFields()) {
                        JField instanceField = store.getFieldRef().resolve();
                        InstanceField targetPtr = csManager.getInstanceField(csObj, instanceField);
                        CSVar sourcePtr = csManager.getCSVar(context, store.getRValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    for (LoadField load : var.getLoadFields()) {
                        JField instanceField = load.getFieldRef().resolve();
                        InstanceField sourcePtr = csManager.getInstanceField(csObj, instanceField);
                        CSVar targetPtr = csManager.getCSVar(context, load.getLValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    for (StoreArray store : var.getStoreArrays()) {
                        ArrayIndex targetPtr = csManager.getArrayIndex(csObj);
                        CSVar sourcePtr = csManager.getCSVar(context, store.getRValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    for (LoadArray load : var.getLoadArrays()) {
                        ArrayIndex sourcePtr = csManager.getArrayIndex(csObj);
                        CSVar targetPtr = csManager.getCSVar(context, load.getLValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet currentSet = pointer.getPointsToSet();
        if (!pointsToSet.isEmpty()) {
            for (CSObj csObj : pointsToSet) {
                if (currentSet.addObject(csObj)) {
                    delta.addObject(csObj);
                }
            }
            for (Pointer succPtr : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succPtr, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var recvVar = recv.getVar();
        Context recvContext = recv.getContext();
        for (Invoke callSite : recvVar.getInvokes()) {
            JMethod method = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(recvContext, callSite);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, method);
            CSMethod csMethod = csManager.getCSMethod(calleeContext, method);

            CSVar thisPtr = csManager.getCSVar(calleeContext, method.getIR().getThis());
            workList.addEntry(thisPtr, PointsToSetFactory.make(recvObj));

            CallKind callKind;
            if (callSite.isStatic()) { callKind = CallKind.STATIC; }
            else if (callSite.isSpecial()) { callKind = CallKind.SPECIAL; }
            else if (callSite.isInterface()) { callKind = CallKind.INTERFACE; }
            else if (callSite.isVirtual()) { callKind = CallKind.VIRTUAL; }
            else if (callSite.isDynamic()) { callKind = CallKind.DYNAMIC; }
            else { callKind = CallKind.OTHER; }

            if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csMethod))) {
                handleNewReachableMethod(csMethod, csCallSite);
            }
        }
    }

    private void handleNewReachableMethod(CSMethod csMethod, CSCallSite csCallSite) {
        addReachable(csMethod);
        JMethod method = csMethod.getMethod();
        Invoke callSite = csCallSite.getCallSite();
        Context calleeContext = csMethod.getContext();
        Context recvContext = csCallSite.getContext();
        for (int i = 0; i < method.getParamCount(); ++i) {
            CSVar sourcePtr = csManager.getCSVar(recvContext, callSite.getInvokeExp().getArg(i));
            CSVar targetPtr = csManager.getCSVar(calleeContext, method.getIR().getParam(i));
            addPFGEdge(sourcePtr, targetPtr);
        }
        Var resultVar = callSite.getResult();
        if (resultVar != null) {
            CSVar resultPtr = csManager.getCSVar(recvContext, resultVar);
            for (Var returnVar : method.getIR().getReturnVars()) {
                CSVar returnPtr = csManager.getCSVar(calleeContext, returnVar);
                addPFGEdge(returnPtr, resultPtr);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
