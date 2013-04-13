using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    public class VariableIndexed : Variable
    {
        public VariableIndexed(string name, string rate, VarType type, VarUpdateType update_type, string initial) 
            : base(name, rate, type, update_type, initial)
        {
            // indexed variables only
            Expr h = Controller.Instance.Z3.MkIntConst("h"); // todo: vs Controller.Instance.IndexType
            BoolExpr idxConstraint = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.IndexOne, (ArithExpr)h), Controller.Instance.Z3.MkLe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexN));

            switch (this.Type)
            {
                case Variable.VarType.location:
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    Sort locSort = Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType);
                                    ArrayExpr q = (ArrayExpr)Controller.Instance.Z3.MkConst("q", locSort); // control location; todo: should map to finite control state (just hack to use integers for now)
                                    Controller.Instance.DataA.IndexedVariableDecl.Add("q", q);
                                    ArrayExpr qPrime = (ArrayExpr)Controller.Instance.Z3.MkConst("q" + Controller.PRIME_SUFFIX, locSort); ; // control location; todo: should map to finite control state (just hack to use integers for now)
                                    Controller.Instance.DataA.IndexedVariableDeclPrimed.Add("q", qPrime);

                                    // apply each index to the control location function
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(this.ValueA))
                                        {
                                            Controller.Instance.DataA.IndexedVariableDecl.Add(this.Name, this.ValueA);
                                            Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimedA);
                                        }
                                    }
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    //FuncDecl q = Controller.Instance.Z3.MkFuncDecl("q", Controller.Instance.IndexType, Controller.Instance.LocType); // control location; todo: should map to finite control state (just hack to use integers for now)
                                    //Controller.Instance.DataU.IndexedVariableDecl.Add("q", q);
                                    //FuncDecl qPrime = Controller.Instance.Z3.MkFuncDecl("q" + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.LocType); // control location; todo: should map to finite control state (just hack to use integers for now)
                                    //Controller.Instance.DataU.IndexedVariableDeclPrimed.Add("q", qPrime);

                                    this.Value = Controller.Instance.Z3.MkFuncDecl(this.Name, Controller.Instance.IndexType, Controller.Instance.LocType);
                                    this.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.LocType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(this.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(this.Name, this.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimed);
                                    }

                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }
                        }
                        break;
                    }
                case Variable.VarType.boolean:
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    this.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort()));
                                    this.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort()));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(this.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(this.Name, this.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimedA);
                                    }

                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    this.Value = Controller.Instance.Z3.MkFuncDecl(this.Name, Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort());
                                    this.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort());

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(this.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(this.Name, this.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimed);
                                    }

                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }
                        }
                        break;
                    }
                case Variable.VarType.integer:
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    this.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType));
                                    this.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(this.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(this.Name, this.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimedA);
                                    }

                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    this.Value = Controller.Instance.Z3.MkFuncDecl(this.Name, Controller.Instance.IndexType, Controller.Instance.IntType);
                                    this.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.IntType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(this.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(this.Name, this.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimed);
                                    }

                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }
                        }
                        break;
                    }
                case Variable.VarType.real:
                    {
                        this.makeRealContinuousVar(); // couldn't do a fall-through for some reason, so using a simple function
                        break;
                    }

                case Variable.VarType.nnreal:
                    {
                        this.makeRealContinuousVar();

                        // assume non-negative
                        // x
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    Expr cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[this.Name], h), (ArithExpr)Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // x'
                                    cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[this.Name], h), Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    Expr cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[this.Name], h), Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // x'
                                    cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[this.Name], h), Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }
                        }
                        break;
                    }

                case Variable.VarType.index:
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    this.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IndexType));
                                    this.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IndexType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(this.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(this.Name, this.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimedA);
                                    }

                                    //why doing this for index type?
                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Expr cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[this.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[this.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // p'
                                    cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[this.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[this.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    this.Value = Controller.Instance.Z3.MkFuncDecl(this.Name, Controller.Instance.IndexType, Controller.Instance.IndexType);
                                    this.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.IndexType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(this.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(this.Name, this.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimed);
                                    }

                                    // why doing this for index type?...
                                    //this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Expr cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[this.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[this.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // p'
                                    cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[this.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[this.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }
                        }
                        break;
                    }

                default:
                    {
                        break;
                    }
            }

            this.finishConstruction();
        }

        private void makeRealContinuousVar()
        {
            // add function declaration to global function declarations
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                        this.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));
                        this.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));

                        if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(this.ValueA))
                        {
                            Controller.Instance.DataA.IndexedVariableDecl.Add(this.Name, this.ValueA);
                            Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimedA);
                        }

                        this.ValueRateA = (ArrayExpr)Controller.Instance.Z3.MkConst(this.Name + Controller.DOT_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType)); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkSelect(this.ValueA, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkSelect(this.ValuePrimedA, pair.Value));
                        }
                    }
                    break;
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                        this.Value = Controller.Instance.Z3.MkFuncDecl(this.Name, Controller.Instance.IndexType, Controller.Instance.RealType);
                        this.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.RealType);

                        if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(this.Value))
                        {
                            Controller.Instance.DataU.IndexedVariableDecl.Add(this.Name, this.Value);
                            Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(this.Name, this.ValuePrimed);
                        }

                        this.ValueRate = Controller.Instance.Z3.MkFuncDecl(this.Name + Controller.DOT_SUFFIX, Controller.Instance.IndexType, Controller.Instance.RealType); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(this.Name, pair.Key), Controller.Instance.Z3.MkApp(this.Value, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(this.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(this.ValuePrimed, pair.Value));
                        }
                        break;
                    }
            }
        }
    }
}
