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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // initiate all the arguments with NAC
        CPFact fact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // realize the meet operator

        // NAC ∩ v = NAC
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        // UNDEF ∩ v = v
        if (v1.isUndef()) { return v2; }
        if (v2.isUndef()) { return v1; }

        assert v1.isConstant();
        assert v2.isConstant();

        // c0 ∩ c0 = c0
        if (v1.equals(v2)) { return v1; }

        // c1 ∩ c2 = NAC
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // if no definition happens, use identity function
        if (!(stmt instanceof DefinitionStmt<?, ?> definitionStmt)) { return out.copyFrom(in); }

        LValue lValue = definitionStmt.getLValue();
        RValue rValue = definitionStmt.getRValue();

        // temporarily only consider assignment to variable
        // use identity function for other occasions
        if (!(lValue instanceof Var key)) { return out.copyFrom(in); }

        // focus on type "int"
        if (rValue instanceof Var var) {
            if (!canHoldInt(var)) { return out.copyFrom(in); }
        } else if (rValue instanceof BinaryExp binaryExp) {
            if (!(canHoldInt(binaryExp.getOperand1()) && canHoldInt(binaryExp.getOperand2()))) {
                return out.copyFrom(in);
            }
        } else if (rValue instanceof NegExp negExp) {
            if (!canHoldInt(negExp.getOperand())) {
                return out.copyFrom(in);
            }
        }

        // evaluate the abstract value of rValue expression and update the map
        CPFact temp = in.copy();
        temp.update(key, evaluate(rValue, in));
        return out.copyFrom(temp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        // evaluate int literal
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }

        // evaluate variable
        if (exp instanceof Var var) {
            Value value = in.get(var);
            if (value.isConstant()) {
                return Value.makeConstant(value.getConstant());
            }
            if (value.isUndef()) {
                return Value.getUndef();
            }
            return Value.getNAC();
        }

        // evaluate binary expression
        if (exp instanceof BinaryExp binaryExp) {
            if (in.get(binaryExp.getOperand1()).isNAC() || in.get(binaryExp.getOperand2()).isNAC()) {
                return Value.getNAC();
            }
            if (in.get(binaryExp.getOperand1()).isConstant() && in.get(binaryExp.getOperand2()).isConstant()) {
                int value1 = in.get(binaryExp.getOperand1()).getConstant();
                int value2 = in.get(binaryExp.getOperand2()).getConstant();

                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD -> { return Value.makeConstant( value1 + value2); }
                        case MUL -> { return Value.makeConstant( value1 * value2); }
                        case SUB -> { return Value.makeConstant( value1 - value2); }
                        case DIV -> { return value2 == 0 ? Value.getUndef() : Value.makeConstant( value1 / value2); }
                        case REM -> { return value2 == 0 ? Value.getUndef() : Value.makeConstant( value1 % value2); }
                    }
                } else if (exp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> { return Value.makeConstant( value1 << value2); }
                        case SHR -> { return Value.makeConstant( value1 >> value2); }
                        case USHR -> { return Value.makeConstant( value1 >>> value2); }
                    }
                } else if (exp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case OR -> { return Value.makeConstant( value1 | value2); }
                        case AND -> { return Value.makeConstant( value1 & value2); }
                        case XOR -> { return Value.makeConstant( value1 ^ value2); }
                    }
                } else if (exp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ -> { return Value.makeConstant( value1 == value2 ? 1 : 0); }
                        case GE -> { return Value.makeConstant( value1 >= value2 ? 1 : 0); }
                        case GT -> { return Value.makeConstant( value1 > value2 ? 1 : 0); }
                        case LE -> { return Value.makeConstant( value1 <= value2 ? 1 : 0); }
                        case LT -> { return Value.makeConstant( value1 < value2 ? 1 : 0); }
                        case NE -> { return Value.makeConstant( value1 != value2 ? 1 : 0); }
                    }
                }
            }
            return Value.getUndef();
        }

        // evaluate negation
        if (exp instanceof NegExp negExp) {
            if (in.get(negExp.getOperand()).isNAC()) {
                return Value.getNAC();
            }
            if (in.get(negExp.getOperand()).isConstant()) {
                int value = in.get(negExp.getOperand()).getConstant();
                return Value.makeConstant(-value);
            }
            return Value.getUndef();
        }

        // evaluate new expression
        if (exp instanceof NewExp) {
            return Value.getUndef();
        }

        // make the analysis safe
        return Value.getNAC();
    }
}
