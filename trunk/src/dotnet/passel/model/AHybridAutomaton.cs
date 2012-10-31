using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller.smt.z3;

using passel.controller;
using passel.controller.parsing;
using passel.controller.parsing.math;

namespace passel.model
{
    /**
     * Hybrid automaton object
     */
    public abstract class AHybridAutomaton
    {
        /**
         * Parent system (with global variables, assumptions, etc.)
         */
        public Holism Parent;

        /**
         * Default constructor
         */
        public AHybridAutomaton(Holism parent, String name)
        {
            this.Parent = parent;
            this.Name = name;
        }

        public String Name;

        /**
         * Set of variables
         */
        protected IList<Variable> _variables = new List<Variable>();

        /**
         * Set of discrete control locations
         */
        protected ISet<Location> _locations = new HashSet<Location>();

        /**
         * Term representing initial condition
         */
        protected Expr _initial;
        public String InitialString;

        /**
         * Add an array of locations to the set of locations
         */
        public void addLocations(params Location[] locations)
        {
            if (this._locations == null)
            {
                this._locations = new HashSet<Location>();
            }

            for (int i = 0; i < locations.Length; i++)
            {
                this._locations.Add(locations[i]);
            }
        }

        /**
         * Add a location to the set of locations
         */
        public void addLocation(Location s)
        {
            if (this._locations == null)
            {
                this._locations = new HashSet<Location>();
            }
            this._locations.Add(s);
        }

        /**
         * Accessor for locations
         */
        public ISet<Location> Locations
        {
            get { return this._locations; }
            set { this._locations = value; }
        }

        /**
         * Accessor for variables
         */
        public IList<Variable> Variables
        {
            get
            {
                if (this._variables == null)
                {
                    this._variables = new List<Variable>();
                }
                return this._variables;
            }
            set { this._variables = value; }
        }

        /**
         * Return a variable with the specified name if one exists
         */
        public Variable GetVariableByName(String name)
        {
            if (this._variables != null)
            {
                foreach (var v in this._variables)
                {
                    if (v.Name == name)
                    {
                        return v;
                    }
                }
            }
            throw new Exception("Error: did not find variable named " + name + " in the set of variables.");
        }

        /**
         * Accessor for initial term
         */
        public Expr Initial
        {
            get { return this._initial; }
            set { this._initial = value; }
        }

        private Variable makeRealContinuousVar(Variable v)
        {
            // add function declaration to global function declarations
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                        v.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));
                        v.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));

                        if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                        {
                            Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                            Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                        }

                        v.ValueRateA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name + Controller.DOT_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType)); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkSelect(v.ValueA, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkSelect(v.ValuePrimedA, pair.Value));
                        }
                    }
                    break;
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                        v.Value = Controller.Instance.Z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.RealType);
                        v.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.RealType);

                        if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                        {
                            Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                            Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                        }

                        v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IndexType, Controller.Instance.RealType); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                        }
                        break;
                    }
            }
            return v;
        }

        /**
         * Add a new variable of the specified type
         */
        public Variable addIndexedVariable(String name, Variable.VarType type, Variable.VarUpdateType update_type)
        {
            if (this._variables == null)
            {
                this._variables = new List<Variable>();
            }

            Variable v = new Variable(name, "", type);
            v.UpdateType = update_type;

            Expr h = Controller.Instance.Z3.MkIntConst("h"); // todo: vs Controller.Instance.IndexType
            BoolExpr idxConstraint = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.IndexOne, (ArithExpr)h), Controller.Instance.Z3.MkLe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexN));

            switch (v.Type)
            {
                case Variable.VarType.boolean:
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort()));
                                    v.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort()));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    //v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = Controller.Instance.Z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort());
                                    v.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.Z3.MkBoolSort());

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    //v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
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
                                    v.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType));
                                    v.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    //v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = Controller.Instance.Z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.IntType);
                                    v.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.IntType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    //v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }
                        }
                        break;
                    }
                case Variable.VarType.real:
                    {
                        v = this.makeRealContinuousVar(v); // couldn't do a fall-through for some reason, so using a simple function
                        break;
                    }

                case Variable.VarType.nnreal:
                    {
                        v = this.makeRealContinuousVar(v);

                        // assume non-negative
                        // x
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    Expr cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // x'
                                    cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h), Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    Expr cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h), Controller.Instance.RealZero);
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // x'
                                    cnstr = Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h), Controller.Instance.RealZero);
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
                                    v.ValueA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IndexType));
                                    v.ValuePrimedA = (ArrayExpr)Controller.Instance.Z3.MkConst(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IndexType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    //why doing this for index type?
                                    //v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Expr cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // p'
                                    cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = Controller.Instance.Z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.IndexType);
                                    v.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.IndexType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    // why doing this for index type?...
                                    //v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Expr cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // p'
                                    cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
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

            this._variables.Add(v);

            return v;
        }

        /**
         * Locate initial conditions, assert constraints, etc.
         * Called by parser after all objects on which this depends have been instantiated
         */
        public void finishConstruction()
        {
            UInt32 min = UInt32.MaxValue;
            UInt32 max = 0;
            List<BoolExpr> initialStates = new List<BoolExpr>();
            foreach (ConcreteLocation acl in this.Locations)
            {
                max = Math.Max(max, acl.Value);
                min = Math.Min(min, acl.Value);

                // disjunction of all states specified as initial
                if (acl.Initial)
                {
                    initialStates.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Q["i"], acl.ValueTerm));
                }
            }

            Expr indexConstrainti = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Indices["i"], (ArithExpr)Controller.Instance.IndexOne), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Indices["i"], (ArithExpr)Controller.Instance.IndexN));

            // parse initial condition string
            if (this.InitialString != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(this.InitialString);
                this._initial = passel.controller.parsing.math.ast.LogicalExpression.CreateTerm(tmptree);

                if (initialStates.Count > 1)
                {
                    this._initial = Controller.Instance.Z3.MkAnd((BoolExpr)this._initial, Controller.Instance.Z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainti, Controller.Instance.Z3.MkOr((BoolExpr[])initialStates.ToArray())))); // note the or, this is correct, non-deterministic start state
                }
                else if (initialStates.Count == 1)
                {
                    this._initial = Controller.Instance.Z3.MkAnd((BoolExpr)this._initial, Controller.Instance.Z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainti, (BoolExpr)initialStates[0]))); // note the or, this is correct, non-deterministic start state
                }
                else
                {
                    // todo: possibly error
                }
            }
            else
            {
                if (initialStates.Count > 1)
                {
                    this._initial = Controller.Instance.Z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainti, Controller.Instance.Z3.MkOr((BoolExpr[])initialStates.ToArray()))); // note the or, this is correct, non-deterministic start state
                }
                else if (initialStates.Count == 1)
                {
                    this._initial = Controller.Instance.Z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainti, (BoolExpr)initialStates[0])); // note the or, this is correct, non-deterministic start state
                }
                else
                {
                    // todo: definitely error (no i.c.)
                }
            }

            //Controller.Instance.Z3.AssertCnstr(this._initial); // assert the initial constraint; actually, don't want to assert this for inductive invariant checking

            Expr int_maxState = Controller.Instance.Z3.MkInt(max);

            // assign names to the location constants (otherwise we can get in scenarios where all combinatorial assignments to location names show up)
            for (UInt32 i = min; i <= max; i++)
            {
                Controller.Instance.Z3.AssumptionsUniversal.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Locations[Controller.Instance.LocationNumToName[(uint)i]], Controller.Instance.Z3.MkBV(i, Controller.Instance.LocSize)));
            }

            Controller.Instance.Z3.AssumptionsUniversal.Add(Controller.Instance.Z3.MkDistinct(Controller.Instance.Locations.Values.ToArray())); // assert all control locations are different locations
            List<BoolExpr> controlRangeList = new List<BoolExpr>();
            Expr iidx = Controller.Instance.Indices["i"];
            foreach (var v in Controller.Instance.Locations.Values.ToArray())
            {
                controlRangeList.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], iidx), v));
            }
            BoolExpr controlRange;
            if (controlRangeList.Count > 1)
            {
                controlRange = Controller.Instance.Z3.MkForall(new Expr[] { iidx }, Controller.Instance.Z3.MkOr(controlRangeList.ToArray()));
            }
            else
            {
                controlRange = Controller.Instance.Z3.MkForall(new Expr[] { iidx }, controlRangeList[0]); // todo: error handling...what if 0?
            }

            Controller.Instance.Z3.Assumptions.Add(controlRange); // assert all processes must stay inside control range bounds



            // bound domain of control locations
            // q
            Expr h = Controller.Instance.Indices["i"];
            Expr indexConstrainth = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexOne), Controller.Instance.Z3.MkLe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexN));
            //Expr indexConstrainth = Controller.Instance.Z3.MkTrue();

            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        Expr cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl["q"], h), (ArithExpr)Controller.Instance.IntZero), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl["q"], h), (ArithExpr)int_maxState));
                        Expr fc = Controller.Instance.Z3.MkForall(new Expr[] { h }, cnstr); // forall indices h, enforce location bounds on q
                        Controller.Instance.Z3.Assumptions.Add((BoolExpr)fc);

                        // q'
                        //Controller.Instance.IntOne <= h & h <= Controller.Instance.Params["N"] &
                        cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed["q"], h), (ArithExpr)Controller.Instance.IntZero), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed["q"], h), (ArithExpr)int_maxState));
                        fc = Controller.Instance.Z3.MkForall(new Expr[] { h }, cnstr);
                        Controller.Instance.Z3.Assumptions.Add((BoolExpr)fc);
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        //Expr cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], h), (ArithExpr)Controller.Instance.IntZero), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], h), (ArithExpr)int_maxState));
                        //Expr fc = Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainth, (BoolExpr)cnstr)); // forall indices h, enforce location bounds on q
                        // oldest //Expr fc = Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr); // forall indices h, enforce location bounds on q
                        //Controller.Instance.Z3.Assumptions.Add((BoolExpr)fc);

                        // q'
                        //Controller.Instance.IntOne <= h & h <= Controller.Instance.Params["N"] &
                        //cnstr = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed["q"], h), (ArithExpr)Controller.Instance.IntZero), Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed["q"], h), (ArithExpr)int_maxState));
                        //fc = Controller.Instance.Z3.MkForall(new Expr[] { h }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainth, (BoolExpr)cnstr));
                        // oldest //fc = Controller.Instance.Z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr);
                        //Controller.Instance.Z3.Assumptions.Add((BoolExpr)fc);
                        break;
                    }
            }
        }
    }
}
