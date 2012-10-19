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
        public static Z3Wrapper z3 = Controller.Instance.Z3;

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
                        v.ValueA = (ArrayExpr)z3.MkConst(v.Name, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));
                        v.ValuePrimedA = (ArrayExpr)z3.MkConst(v.Name + Controller.PRIME_SUFFIX, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));

                        if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                        {
                            Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                            Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                        }

                        v.ValueRateA = (ArrayExpr)z3.MkConst(v.Name + Controller.DOT_SUFFIX, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType)); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkSelect(v.ValueA, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkSelect(v.ValuePrimedA, pair.Value));
                        }
                    }
                    break;
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                        v.Value = z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.RealType);
                        v.ValuePrimed = z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.RealType);

                        if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                        {
                            Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                            Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                        }

                        v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IndexType, Controller.Instance.RealType); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
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

            Expr h = z3.MkIntConst("h"); // todo: vs Controller.Instance.IndexType
            BoolExpr idxConstraint = z3.MkAnd(z3.MkLe((ArithExpr)Controller.Instance.IndexOne, (ArithExpr)h), z3.MkLe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexN));

            switch (v.Type)
            {
                case Variable.VarType.boolean:
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.ValueA = (ArrayExpr)z3.MkConst(v.Name, z3.MkArraySort(Controller.Instance.IndexType, z3.MkBoolSort()));
                                    v.ValuePrimedA = (ArrayExpr)z3.MkConst(v.Name + Controller.PRIME_SUFFIX, z3.MkArraySort(Controller.Instance.IndexType, z3.MkBoolSort()));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    //v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, z3.MkBoolSort());
                                    v.ValuePrimed = z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, z3.MkBoolSort());

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    //v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
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
                                    v.ValueA = (ArrayExpr)z3.MkConst(v.Name, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType));
                                    v.ValuePrimedA = (ArrayExpr)z3.MkConst(v.Name + Controller.PRIME_SUFFIX, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IntType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    //v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
                                    }
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.IntType);
                                    v.ValuePrimed = z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.IntType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    //v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
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
                                    Expr cnstr = z3.MkGe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.RealZero);
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // x'
                                    cnstr = z3.MkGe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h), Controller.Instance.RealZero);
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    Expr cnstr = z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h), Controller.Instance.RealZero);
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // x'
                                    cnstr = z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h), Controller.Instance.RealZero);
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
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
                                    v.ValueA = (ArrayExpr)z3.MkConst(v.Name, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IndexType));
                                    v.ValuePrimedA = (ArrayExpr)z3.MkConst(v.Name + Controller.PRIME_SUFFIX, z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.IndexType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    //why doing this for index type?
                                    //v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Expr cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), z3.MkLe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // p'
                                    cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), z3.MkLe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.IndexType);
                                    v.ValuePrimed = z3.MkFuncDecl(v.Name + Controller.PRIME_SUFFIX, Controller.Instance.IndexType, Controller.Instance.IndexType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    // why doing this for index type?...
                                    //v.ValueRate = z3.MkFuncDecl(v.Name + Controller.DOT_SUFFIX, Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + Controller.PRIME_SUFFIX, pair.Key), z3.MkApp(v.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Expr cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), z3.MkLe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));

                                    // p'
                                    cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexNone), z3.MkLe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h), (ArithExpr)Controller.Instance.IndexN));
                                    z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, z3.MkImplies(idxConstraint, (BoolExpr)cnstr)));
                                    //z3.Assumptions.Add(z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr));
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
                    initialStates.Add(z3.MkEq(Controller.Instance.Q["i"], acl.ValueTerm));
                }
            }

            Expr indexConstrainti = z3.MkAnd(z3.MkGe((ArithExpr)Controller.Instance.Indices["i"], (ArithExpr)Controller.Instance.IndexOne), z3.MkLe((ArithExpr)Controller.Instance.Indices["i"], (ArithExpr)Controller.Instance.IndexN));

            // parse initial condition string
            if (this.InitialString != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(this.InitialString);
                this._initial = passel.controller.parsing.math.ast.LogicalExpression.CreateTerm(tmptree);

                if (initialStates.Count > 1)
                {
                    this._initial = z3.MkAnd((BoolExpr)this._initial, z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, z3.MkImplies((BoolExpr)indexConstrainti, z3.MkOr((BoolExpr[])initialStates.ToArray())))); // note the or, this is correct, non-deterministic start state
                }
                else if (initialStates.Count == 1)
                {
                    this._initial = z3.MkAnd((BoolExpr)this._initial, z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, z3.MkImplies((BoolExpr)indexConstrainti, (BoolExpr)initialStates[0]))); // note the or, this is correct, non-deterministic start state
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
                    this._initial = z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, z3.MkImplies((BoolExpr)indexConstrainti, z3.MkOr((BoolExpr[])initialStates.ToArray()))); // note the or, this is correct, non-deterministic start state
                }
                else if (initialStates.Count == 1)
                {
                    this._initial = z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, z3.MkImplies((BoolExpr)indexConstrainti, (BoolExpr)initialStates[0])); // note the or, this is correct, non-deterministic start state
                }
                else
                {
                    // todo: definitely error (no i.c.)
                }
            }

            //z3.AssertCnstr(this._initial); // assert the initial constraint; actually, don't want to assert this for inductive invariant checking

            Expr int_maxState = z3.MkInt(max);

            // assign names to the location constants (otherwise we can get in scenarios where all combinatorial assignments to location names show up)
            for (UInt32 i = min; i <= max; i++)
            {
                z3.AssumptionsUniversal.Add(z3.MkEq(Controller.Instance.Locations[Controller.Instance.LocationNumToName[(uint)i]], z3.MkBV(i, Controller.Instance.LocSize)));
            }

            z3.AssumptionsUniversal.Add(z3.MkDistinct(Controller.Instance.Locations.Values.ToArray())); // assert all control locations are different locations
            List<BoolExpr> controlRangeList = new List<BoolExpr>();
            Expr iidx = Controller.Instance.Indices["i"];
            foreach (var v in Controller.Instance.Locations.Values.ToArray())
            {
                controlRangeList.Add(z3.MkEq(z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], iidx), v));
            }
            BoolExpr controlRange;
            if (controlRangeList.Count > 1)
            {
                controlRange = z3.MkForall(new Expr[] { iidx }, z3.MkOr(controlRangeList.ToArray()));
            }
            else
            {
                controlRange = z3.MkForall(new Expr[] { iidx }, controlRangeList[0]); // todo: error handling...what if 0?
            }

            z3.Assumptions.Add(controlRange); // assert all processes must stay inside control range bounds



            // bound domain of control locations
            // q
            Expr h = Controller.Instance.Indices["i"];
            Expr indexConstrainth = z3.MkAnd(z3.MkGe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexOne), z3.MkLe((ArithExpr)h, (ArithExpr)Controller.Instance.IndexN));
            //Expr indexConstrainth = z3.MkTrue();

            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        Expr cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl["q"], h), (ArithExpr)Controller.Instance.IntZero), z3.MkLe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl["q"], h), (ArithExpr)int_maxState));
                        Expr fc = z3.MkForall(new Expr[] { h }, cnstr); // forall indices h, enforce location bounds on q
                        z3.Assumptions.Add((BoolExpr)fc);

                        // q'
                        //Controller.Instance.IntOne <= h & h <= Controller.Instance.Params["N"] &
                        cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed["q"], h), (ArithExpr)Controller.Instance.IntZero), z3.MkLe((ArithExpr)z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed["q"], h), (ArithExpr)int_maxState));
                        fc = z3.MkForall(new Expr[] { h }, cnstr);
                        z3.Assumptions.Add((BoolExpr)fc);
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        //Expr cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], h), (ArithExpr)Controller.Instance.IntZero), z3.MkLe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], h), (ArithExpr)int_maxState));
                        //Expr fc = z3.MkForall(new Expr[] { h }, z3.MkImplies((BoolExpr)indexConstrainth, (BoolExpr)cnstr)); // forall indices h, enforce location bounds on q
                        // oldest //Expr fc = z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr); // forall indices h, enforce location bounds on q
                        //z3.Assumptions.Add((BoolExpr)fc);

                        // q'
                        //Controller.Instance.IntOne <= h & h <= Controller.Instance.Params["N"] &
                        //cnstr = z3.MkAnd(z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed["q"], h), (ArithExpr)Controller.Instance.IntZero), z3.MkGe((ArithExpr)z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed["q"], h), (ArithExpr)int_maxState));
                        //fc = z3.MkForall(new Expr[] { h }, z3.MkImplies((BoolExpr)indexConstrainth, (BoolExpr)cnstr));
                        // oldest //fc = z3.MkForall(new Expr[] { h }, (BoolExpr)cnstr);
                        //z3.Assumptions.Add((BoolExpr)fc);
                        break;
                    }
            }
        }
    }
}
