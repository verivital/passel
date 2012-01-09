using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;
using phyea.controller.parsing;
using phyea.controller.parsing.math;

namespace phyea.model
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
        public AHybridAutomaton(Holism parent)
        {
            this.Parent = parent;
        }

        /**
         * Set of variables
         */
        protected ISet<Variable> _variables = new HashSet<Variable>();

        /**
         * Set of discrete control locations
         */
        protected ISet<Location> _locations = new HashSet<Location>();

        /**
         * Term representing initial condition
         */
        protected Term _initial;
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
        public ISet<Variable> Variables
        {
            get
            {
                if (this._variables == null)
                {
                    this._variables = new HashSet<Variable>();
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
        public Term Initial
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
                        v.ValueA = Controller.Instance.Z3.MkConst(v.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));
                        v.ValuePrimedA = Controller.Instance.Z3.MkConst(v.Name + "'", Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType));

                        if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                        {
                            Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                            Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                        }

                        v.ValueRateA = Controller.Instance.Z3.MkConst(v.Name + "_dot", Controller.Instance.Z3.MkArraySort(Controller.Instance.IndexType, Controller.Instance.RealType)); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkArraySelect(v.ValueA, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + "'", pair.Key), Controller.Instance.Z3.MkArraySelect(v.ValuePrimedA, pair.Value));
                        }
                    }
                    break;
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                        v.Value = Controller.Instance.Z3.MkFuncDecl(v.Name, Controller.Instance.IndexType, Controller.Instance.RealType);
                        v.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(v.Name + "'", Controller.Instance.IndexType, Controller.Instance.RealType);

                        if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                        {
                            Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                            Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                        }

                        v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + "_dot", Controller.Instance.IndexType, Controller.Instance.RealType); // todo: only do this if continuous update_type
                        foreach (var pair in Controller.Instance.Indices)
                        {
                            Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                            Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + "'", pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
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
                this._variables = new HashSet<Variable>();
            }

            Variable v = new Variable(name, "", type);
            v.UpdateType = update_type;

            switch (v.Type)
            {
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
                        Term h = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);

                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    Term cnstr = Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h) >= Controller.Instance.RealZero;
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));

                                    // x'
                                    cnstr = Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h) >= Controller.Instance.RealZero;
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    Term cnstr = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h) >= Controller.Instance.RealZero;
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));

                                    // x'
                                    cnstr = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h) >= Controller.Instance.RealZero;
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));
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
                                    v.ValueA = Controller.Instance.Z3.MkConst(v.Name, Controller.Instance.Z3.MkArraySort(Controller.Instance.IntType, Controller.Instance.IntType));
                                    v.ValuePrimedA = Controller.Instance.Z3.MkConst(v.Name + "'", Controller.Instance.Z3.MkArraySort(Controller.Instance.IntType, Controller.Instance.IntType));

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsValue(v.ValueA))
                                    {
                                        Controller.Instance.DataA.IndexedVariableDecl.Add(v.Name, v.ValueA);
                                        Controller.Instance.DataA.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimedA);
                                    }

                                    v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + "_dot", Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + "'", pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Term h = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);
                                    Term cnstr = Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDecl[v.Name], h) <= Controller.Instance.Params["N"];
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));

                                    // p'
                                    h = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType); // get fresh just in case
                                    cnstr = Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], h) <= Controller.Instance.Params["N"];
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));
                                    break;
                                }

                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    // todo: pull these common parts out for all "real" types (then only enforce the nnreal or posreal part)
                                    v.Value = Controller.Instance.Z3.MkFuncDecl(v.Name, Controller.Instance.IntType, Controller.Instance.IntType);
                                    v.ValuePrimed = Controller.Instance.Z3.MkFuncDecl(v.Name + "'", Controller.Instance.IntType, Controller.Instance.IntType);

                                    // add function declaration to global function declarations
                                    if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsValue(v.Value))
                                    {
                                        Controller.Instance.DataU.IndexedVariableDecl.Add(v.Name, v.Value);
                                        Controller.Instance.DataU.IndexedVariableDeclPrimed.Add(v.Name, v.ValuePrimed);
                                    }

                                    v.ValueRate = Controller.Instance.Z3.MkFuncDecl(v.Name + "_dot", Controller.Instance.IntType, Controller.Instance.IntType); // todo: only do this if continuous update_type
                                    foreach (var pair in Controller.Instance.Indices)
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<String, String>(v.Name, pair.Key), Controller.Instance.Z3.MkApp(v.Value, pair.Value));
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<String, String>(v.Name + "'", pair.Key), Controller.Instance.Z3.MkApp(v.ValuePrimed, pair.Value));
                                    }

                                    // p and p' constraints
                                    // pointer variables take values in the set of indices (i.e., 1 <= p[i] <= N, or p[i] = 0 = \bot)
                                    // p
                                    Term h = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);
                                    Term cnstr = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v.Name], h) <= Controller.Instance.Params["N"];
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));

                                    // p'
                                    h = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType); // get fresh just in case
                                    cnstr = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], h) <= Controller.Instance.Params["N"];
                                    Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, Controller.Instance.Z3.MkImplies(Controller.Instance.IndexOne <= h & h <= Controller.Instance.IndexN, cnstr)));
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
            UInt32 max = 0;
            List<Term> initialStates = new List<Term>();
            foreach (ConcreteLocation acl in this.Locations)
            {
                max = Math.Max(max, acl.Value);

                // disjunction of all states specified as initial
                if (acl.Initial)
                {
                    initialStates.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Q["i"], acl.StateValue));
                }
            }

            // parse initial condition string
            if (this.InitialString != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = phyea.controller.parsing.math.Expression.Parse(this.InitialString);
                this._initial = phyea.controller.parsing.math.ast.LogicalExpression.CreateTerm(tmptree);
                this._initial = this._initial & Controller.Instance.Z3.MkForall(0, new Term[] { Controller.Instance.Indices["i"] }, null, Controller.Instance.Z3.MkOr(initialStates.ToArray())); // note the or, this is correct, non-deterministic start state
            }
            else
            {
                this._initial = Controller.Instance.Z3.MkForall(0, new Term[] { Controller.Instance.Indices["i"] }, null, Controller.Instance.Z3.MkOr(initialStates.ToArray())); // note the or, this is correct, non-deterministic start state
            }

            //Controller.Instance.Z3.AssertCnstr(this._initial); // assert the initial constraint; actually, don't want to assert this for inductive invariant checking

            Term int_maxState = Controller.Instance.Z3.MkIntNumeral(max);

            // bound domain of control locations
            // q
            Term h = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);

            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        Term cnstr = Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDecl["q"], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDecl["q"], h) <= int_maxState;
                        Term fc = Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, cnstr); // forall indices h, enforce location bounds on q
                        Controller.Instance.Z3.AssertCnstr(fc);

                        // q'
                        //Controller.Instance.IntOne <= h & h <= Controller.Instance.Params["N"] &
                        cnstr = Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDeclPrimed["q"], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkArraySelect(Controller.Instance.DataA.IndexedVariableDeclPrimed["q"], h) <= int_maxState;
                        fc = Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, cnstr);
                        Controller.Instance.Z3.AssertCnstr(fc);
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        Term cnstr = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], h) <= int_maxState;
                        Term fc = Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, cnstr); // forall indices h, enforce location bounds on q
                        Controller.Instance.Z3.AssertCnstr(fc);

                        // q'
                        //Controller.Instance.IntOne <= h & h <= Controller.Instance.Params["N"] &
                        cnstr = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed["q"], h) >= Controller.Instance.IntZero & Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed["q"], h) <= int_maxState;
                        fc = Controller.Instance.Z3.MkForall(0, new Term[] { h }, null, cnstr);
                        Controller.Instance.Z3.AssertCnstr(fc);
                        break;
                    }
            }

            Controller.Instance.N = Controller.Instance.Params["N"];
        }
    }
}
