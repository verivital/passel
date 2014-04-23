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
    public enum outmode { MODE_PHAVER, MODE_SPACEEX, MODE_HYTECH, MODE_UPPAAL, MODE_LATEX };

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

            this.addIndexedVariable("q", Variable.VarType.location, Variable.VarUpdateType.discrete, null); // control location added by default
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
        public Expr Initial;
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
         * Add a new variable of the specified type
         */
        public Variable addIndexedVariable(String name, Variable.VarType type, Variable.VarUpdateType update_type, String initially)
        {
            if (this._variables == null)
            {
                this._variables = new List<Variable>();
            }

            Variable v = new VariableIndexed(name, "", type, update_type, initially);
            v.UpdateType = update_type;

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
                    initialStates.Add(Controller.Instance.Z3.MkEq(Controller.Instance.IndexedVariables[new KeyValuePair<string, string>("q", "i")], acl.ValueTerm));
                }
            }

            Expr indexConstrainti = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Indices["i"], (ArithExpr)Controller.Instance.IndexOne), Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Indices["i"], (ArithExpr)Controller.Instance.IndexN));


            List<BoolExpr> icsGlobal = new List<BoolExpr>();
            // parse initial condition string
            foreach (var v in this.Parent.Variables)
            {
                if (v.Initially != null)
                {
                    icsGlobal.Add((BoolExpr)v.Initially);
                }
            }

            List<BoolExpr> icsLocal = new List<BoolExpr>();
            // parse initial condition string
            foreach (var v in this.Variables)
            {
                if (v.Initially != null)
                {
                    icsLocal.Add((BoolExpr)v.Initially);
                }
            }

            bool addGeneral = false;

            BoolExpr initLocal = Controller.Instance.Z3.MkTrue();
            if (icsLocal.Count > 1)
            {
                initLocal = Controller.Instance.Z3.MkAnd(icsLocal.ToArray());
            }
            else if (icsLocal.Count == 1)
            {
                initLocal = icsLocal[0];
            }
            else
            {
                if (this.Variables.Count > 1)
                {
                    System.Console.WriteLine("WARNING: Initial condition constraints not specified for variables, assuming any values for variables (i.e., the whole state space intersected with the initial control locations).  This is likely unintentional.");
                }
                //this.Initial = Controller.Instance.Z3.MkTrue(); // any state, unspecified i.c.
            }

            BoolExpr initGlobal = Controller.Instance.Z3.MkTrue();
            if (icsGlobal.Count > 1)
            {
                initGlobal = Controller.Instance.Z3.MkAnd(icsGlobal.ToArray());
            }
            else if (icsGlobal.Count == 1)
            {
                initGlobal = icsGlobal[0];
            }
            else
            {
                if (this.Parent.Variables.Count > 0)
                {
                    System.Console.WriteLine("WARNING: Initial condition constraints not specified for variables, assuming any values for variables (i.e., the whole state space intersected with the initial control locations).  This is likely unintentional.");
                }
                //this.Initial = Controller.Instance.Z3.MkTrue(); // any state, unspecified i.c.
            }

            BoolExpr ic = Controller.Instance.Z3.MkTrue();
            if (this.InitialString != null && this.InitialString.Length > 0)
            {
                // TODO: deprecate / generalize the initial condition in variable method to allow x[i] != x[j]
                Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(this.InitialString);
                ic = (BoolExpr)passel.controller.parsing.math.ast.LogicalExpression.CreateTerm(tmptree);
                addGeneral = true;
            }

            if (initialStates.Count > 1)
            {
                this.Initial = Controller.Instance.Z3.MkAnd((BoolExpr)initGlobal, Controller.Instance.Z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainti, Controller.Instance.Z3.MkAnd((BoolExpr)initLocal, Controller.Instance.Z3.MkOr((BoolExpr[])initialStates.ToArray()))))); // note the or, this is correct, non-deterministic start state
            }
            else if (initialStates.Count == 1)
            {
                this.Initial = Controller.Instance.Z3.MkAnd((BoolExpr)initGlobal, Controller.Instance.Z3.MkForall(new Expr[] { Controller.Instance.Indices["i"] }, Controller.Instance.Z3.MkImplies((BoolExpr)indexConstrainti, Controller.Instance.Z3.MkAnd((BoolExpr)initLocal, (BoolExpr)initialStates[0])))); // note the or, this is correct, non-deterministic start state
            }
            else
            {
                // todo: possibly error
            }

            if (addGeneral)
            {
                this.Initial = Controller.Instance.Z3.MkAnd(ic, (BoolExpr)this.Initial);
            }

            //Controller.Instance.Z3.AssertCnstr(this._initial); // assert the initial constraint; actually, don't want to assert this for inductive invariant checking

            Expr int_maxState = Controller.Instance.Z3.MkInt(max);

            // assign names to the location constants (otherwise we can get in scenarios where all combinatorial assignments to location names show up)
            for (UInt32 i = min; i <= max; i++)
            {
                Controller.Instance.Z3.AssumptionsUniversal.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Locations[Controller.Instance.LocationNumToName[(uint)i]], Controller.Instance.Z3.MkBV(i, Controller.Instance.LocSize)));
            }

            // hack for symmetric reachability (z3 will autoconvert to != if less than 3...)
            if (Controller.Instance.Locations.Count >= 3)
            {
                Controller.Instance.Z3.AssumptionsUniversal.Add(Controller.Instance.Z3.MkDistinct(Controller.Instance.Locations.Values.ToArray())); // assert all control locations are different locations
            }
            else if (Controller.Instance.Locations.Count == 2)
            {
                Controller.Instance.Z3.AssumptionsUniversal.Add(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(Controller.Instance.Locations.Values.First(), Controller.Instance.Locations.Values.Last()))); // assert all control locations are different locations
            }
            List<BoolExpr> controlRangeList = new List<BoolExpr>();
            Expr iidx = Controller.Instance.Indices["i"];
            foreach (var v in Controller.Instance.Locations.Values.ToArray())
            {
                controlRangeList.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], iidx), v));
            }
            BoolExpr controlRange;
            BoolExpr controlRangePrime;
            if (controlRangeList.Count > 1)
            {
                controlRange = Controller.Instance.Z3.MkForall(new Expr[] { iidx }, Controller.Instance.Z3.MkOr(controlRangeList.ToArray()));
                controlRangePrime = Controller.Instance.Z3.MkForall(new Expr[] { iidx }, Controller.Instance.Z3.MkOr(controlRangeList.ToArray()).Substitute(Controller.Instance.IndexedVariables[new KeyValuePair<string,string>("q", "i")], Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string,string>("q" + Controller.PRIME_SUFFIX, "i")] ));
            }
            else
            {
                controlRange = Controller.Instance.Z3.MkForall(new Expr[] { iidx }, controlRangeList[0]); // todo: error handling...what if 0?
                controlRangePrime = Controller.Instance.Z3.MkForall(new Expr[] { iidx }, controlRangeList[0].Substitute(Controller.Instance.IndexedVariables[new KeyValuePair<string, string>("q", "i")], Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>("q" + Controller.PRIME_SUFFIX, "i")]));
            }

            Controller.Instance.Z3.Assumptions.Add(controlRange); // assert all processes must stay inside control range bounds
            Controller.Instance.Z3.Assumptions.Add(controlRangePrime); // assert all processes must stay inside control range bounds



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

        /**
        * Generate a specification of N (for a fixed natural number) automata for Phaver
        */
        public String outputNetworkN(string fnall, uint N, String output_path, String newInitial, uint iteration, outmode mode)
        {
            String spec = "";
            String tmp = "";

            ConcreteHybridAutomaton h = (ConcreteHybridAutomaton)this;

            System.Console.WriteLine("START: Generating phaver/spaceex input file from Passel description for N = " + N);

            const string PHAVER_AUTOMATON = "automaton";
            const string PHAVER_VAR_CONTR = "contr_var";
            const string PHAVER_VAR_INPUT = "input_var";
            const string PHAVER_SYNC_LABEL = "synclabs";
            const string PHAVER_ENDLINE = ";";
            const string PHAVER_SEPARATOR = ":";
            const string PHAVER_LOCATION = "loc";
            const string PHAVER_INVARIANT = "while";
            const string PHAVER_GUARD = "when";
            const string PHAVER_SYNC = "sync";

            const string SPACEEX_AUTOMATON = "automaton";
            const string SPACEEX_VAR_CONTR = "contr_var";
            const string SPACEEX_VAR_INPUT = "input_var";
            const string SPACEEX_SYNC_LABEL = "synclabs";
            const string SPACEEX_ENDLINE = ";";
            const string SPACEEX_SEPARATOR = ":";
            const string SPACEEX_LOCATION = "loc";
            const string SPACEEX_INVARIANT = "while";
            const string SPACEEX_GUARD = "when";
            const string SPACEEX_SYNC = "sync";

            string out_automaton;
            string out_var_contr;
            string out_var_input;
            string out_endline;
            string out_sync;
            string out_sync_label;
            string out_location;
            string out_invariant;
            string out_guard;
            string out_separator;

            List<String> globalSyncLabels = new List<string>();
            Dictionary<String, IList<Variable>> globalSyncLabelsToResetGlobals = new Dictionary<string, IList<Variable>>();  // map global sync labels to global variables (for identity resets)

            string newline = "\n";

            switch (mode)
            {
                case outmode.MODE_SPACEEX:
                    {
                        out_automaton = SPACEEX_AUTOMATON;
                        out_var_contr = SPACEEX_VAR_CONTR;
                        out_var_input = SPACEEX_VAR_INPUT;
                        out_endline = SPACEEX_ENDLINE;
                        out_separator = SPACEEX_SEPARATOR;
                        out_sync = SPACEEX_SYNC;
                        out_sync_label = SPACEEX_SYNC_LABEL;
                        out_location = SPACEEX_LOCATION;
                        out_invariant = SPACEEX_INVARIANT;
                        out_guard = SPACEEX_GUARD;
                        break;
                    }
                case outmode.MODE_PHAVER:
                default:
                    {
                        out_automaton = PHAVER_AUTOMATON;
                        out_var_contr = PHAVER_VAR_CONTR;
                        out_var_input = PHAVER_VAR_INPUT;
                        out_endline = PHAVER_ENDLINE;
                        out_separator = PHAVER_SEPARATOR;
                        out_sync = PHAVER_SYNC;
                        out_sync_label = PHAVER_SYNC_LABEL;
                        out_location = PHAVER_LOCATION;
                        out_invariant = PHAVER_INVARIANT;
                        out_guard = PHAVER_GUARD;

                        break;
                    }
            }

            if (mode == outmode.MODE_PHAVER)
            {
                if (this.Variables.All(v => v.UpdateType != Variable.VarUpdateType.continuous) && this.Parent.Variables.All(v => v.UpdateType != Variable.VarUpdateType.continuous))
                {
                    spec += "ELAPSE_TIME = false; // no continuously updated variables found, preventing time-elapse (trajectories)" + newline;
                }

                spec += "REACH_USE_CONVEX_HULL = false; // not possible with global index variables" + newline +
                        "REACH_MAX_ITER = 0; " + newline +
                        "REACH_USE_BBOX = false;" + newline +
                        "//USE_HIOA_AUTOMATA = true;" + newline +
                        "COMPOSE_USE_CONVEX_HULL_FOR_REACH = false;" + newline +
                        "//COMPOSE_WITH_REACH_MIN = true;" + newline +
                        "CHEAP_CONTAIN_RETURN_OTHERS = false;" + newline + newline;
            }

            // global constants
            if (Controller.Instance.Params.Count > 0)
            {
                foreach (var p in Controller.Instance.Params)
                {
                    spec += p.Key + " := ";
                    if (Controller.Instance.ParamsAssumps.ContainsKey(p.Key))
                    {
                        spec += Controller.Instance.Z3.ToStringFormatted(Controller.Instance.ParamsAssumps[p.Key].Args[1], outmode.MODE_PHAVER, true);
                        // TODO: HACK, ASSUMES ASSUMPTION IS OF THE FORM: PARAMNAME RELATION PARAMVALUE, e.g., N == 3
                    }
                    else
                    {
                        if (p.Key == "N")
                        {
                            spec += N;
                        }
                        else
                        {
                            spec += "1 /* default value, unspecified in source */";
                        }
                    }
                    spec += ";" + newline;
                }
            }
            spec += newline;

            // generate N automata
            for (int i = 1; i <= N; i++)
            {
                // TODO: ADD FUNCTION EVAL AND REMOVE THIS
                /* STARL STUFF
                double x0, y0, xwp, ywp, xr, yr;
                double r = 1;
                x0 = r * Math.Cos((2 * Math.PI) * ((double)i / (double)Controller.Instance.IndexNValue));
                y0 = r * Math.Sin((2 * Math.PI) * ((double)i / (double)Controller.Instance.IndexNValue));

                double delta_max = 0.1;
                double delta_init = 0;

                double delta = 0.0001;
                x0 = Math.Round(x0, 6);
                y0 = Math.Round(y0, 6);

                int k = 1;
                xwp = r * Math.Cos((2 * Math.PI) * ((double)(i+k) / (double)Controller.Instance.IndexNValue));
                ywp = r * Math.Sin((2 * Math.PI) * ((double)(i+k) / (double)Controller.Instance.IndexNValue));

                xwp = Math.Round(xwp, 6);
                ywp = Math.Round(ywp, 6);

                double delta_rate = 0.05;

                xr = (xwp - x0);
                yr = (ywp - y0);

                double xrl, xru, yrl, yru;

                xr = Math.Round(xr, 6);
                yr = Math.Round(yr, 6);

                xrl = xr - delta_rate;
                xru = xr + delta_rate;
                yrl = yr - delta_rate;
                yru = yr + delta_rate;
                 */

                bool hasUguard = false;
                bool hasPointer = false;

                foreach (var l in h.Locations)
                {
                    foreach (var t in l.Transitions)
                    {
                        if (t.UGuard != null)
                        {
                            hasUguard = true;
                            break;
                        }
                    }
                    if (hasUguard)
                    {
                        break;
                    }
                }

                // local pointer/index variables
                foreach (var v in h.Variables.Union(h.Parent.Variables))
                {
                    if (v.Type == Variable.VarType.index)
                    {
                        hasPointer = true;
                        break;
                    }
                }


                spec += out_automaton + " ";
                spec += "agent" + i.ToString() + newline;

                // local variables for A_i 
                if (h.Variables.Count > 1) // avoid q
                {
                    spec += out_var_contr + " " + out_separator + " ";
                    foreach (var v in h.Variables)
                    {
                        if (v.Name == "q")
                        {
                            continue;
                        }
                        spec += v.Name + "_" + i.ToString() + ",";
                    }
                    spec = spec.Substring(0, spec.Length - 1) + out_endline + newline;
                }

                // input variables for A_i: globals or universal guards
                if (this.Parent.Variables.Count > 0 || (hasUguard && N >= 2))
                {
                    spec += out_var_input + " " + out_separator + " ";

                    if (this.Parent.Variables.Count > 0)
                    {
                        foreach (var v in this.Parent.Variables) // globals
                        {
                            spec += v.Name + ",";
                        }
                    }

                    if (hasUguard || hasPointer)
                    {
                        // share all variables of all other processes, so we can conjunct them
                        for (uint j = 1; j <= N; j++)
                        {
                            if (i != j)
                            {
                                foreach (var v in h.Variables)
                                {
                                    if (v.Name == "q")
                                    {
                                        continue;
                                    }
                                    spec += v.Name + "_" + j.ToString() + ",";
                                }
                            }
                        }
                    }

                    spec = spec.Substring(0, spec.Length - 1) + out_endline + newline;
                }

                spec += out_sync_label + " " + out_separator + " " + " tau, ";
                // generate sync label for each transition: iterate over all locations and transitions
                List<String> synclabels = new List<string>();
                foreach (var l in h.Locations)
                {
                    foreach (var t in l.Transitions)
                    {
                        // todo: generate label only if transition is not named
                        foreach (var ns in t.NextStates)
                        {
                            String synclab = l.Label + ns.Label + i.ToString();

                            if (synclabels.Contains(synclab))
                            {
                                synclab += synclabels.Count(
                                        delegate(String s)
                                        {
                                            return s == synclab;
                                        }).ToString();
                            }

                            spec += synclab + ", ";
                            synclabels.Add(synclab);
                        }
                    }
                }
                spec = spec.Substring(0, spec.Length - 2) + out_endline + newline;

                foreach (var l in h.Locations)
                {
                    spec += out_location + " " + l.Label + out_separator + " " + out_invariant + " ";

                    //todo: convert to appropriate format: l.Invariant;
                    if (l.Invariant != null)
                    {
                        tmp = Controller.Instance.Z3.ToStringFormatted(l.Invariant, outmode.MODE_PHAVER, true);
                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                        spec += tmp;
                        spec += " & ";
                    }
                    /*
                    if (l.Stop != null)
                    {
                        // needs to be closure of negation... switch based on strict / nonstrict cases, but how to do in general?
                        tmp = Controller.Instance.Z3.ToStringFormatted(Controller.Instance.Z3.MkNot((BoolExpr)l.Stop), controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true);
                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                        spec += tmp;
                        spec += " & ";
                    }
                     */
                    

                    if (l.Invariant != null || l.Stop != null)
                    {
                        spec = spec.Substring(0, spec.Length - 3);
                    }
                    else
                    {
                        /* STARL stuff
                        double lb, ub;
                        lb = -r - delta_max;
                        ub = r + delta_max;
                        spec += " x_" + i + " >= " + lb + " & x_" + i + " <= " + ub + " & y_" + i + " >= " + lb + " & y_" + i + " <= " + ub + " ";
                         */

                        //double wpdelta = 0.05;
                        //spec += " & (x" + i + " < " + (xwp - wpdelta) + " | x" + i + " > " + (xwp + wpdelta) + " | y" + i + " < " + (ywp - wpdelta) + " | y" + i + " > " + (ywp + wpdelta) + ") ";

                        spec += " true ";
                    }

                    spec += " wait { ";

                    int lbefore = spec.Length;
                    foreach (var f in l.Flows)
                    {
                        // avoid global variables
                        if (Controller.Instance.GlobalVariables.ContainsKey(f.Variable.Name))
                        {
                            continue;
                        }

                        //todo: convert flow appropriately
                        switch (f.DynamicsType)
                        {
                            case Flow.DynamicsTypes.rectangular:
                                {
                                    tmp = f.Variable.Name + "_" + i.ToString() + "' >= " + f.RectRateA.ToString() + " & " + f.Variable + "_" + i.ToString() + "' <= " + f.RectRateB.ToString(); // todo : add rates
                                    break;
                                }
                            case Flow.DynamicsTypes.constant:
                                {
                                    tmp = f.Variable.Name + "_" + i.ToString() + "' == 0";
                                    break;
                                }
                            case Flow.DynamicsTypes.timed: // pass through
                            default:
                                {
                                    tmp = f.Variable.Name + "_" + i.ToString() + "' == " + f.RectRateA;

                                    /* STARL STUFF
                                    if (f.Variable.Name == "x")
                                    {
                                        //tmp = f.Variable.Name + "_" + i + "' == " + xr;
                                        tmp =  f.Variable.Name + "_" + i + "' >= " + xrl + " & ";
                                        tmp += f.Variable.Name + "_" + i + "' <= " + xru;
                                    }
                                    if (f.Variable.Name == "y")
                                    {
                                        //tmp = f.Variable.Name + "_" + i + "' == " + yr;
                                        tmp =  f.Variable.Name + "_" + i + "' >= " + yrl + " & ";
                                        tmp += f.Variable.Name + "_" + i + "' <= " + yru;
                                    }
                                     */

                                    break;
                                }
                        }
                        //tmp = z3.ToStringFormatted(f., controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver);

                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                        spec += tmp;
                        spec += " & ";
                    }

                    foreach (var v in h.Variables)
                    {
                        if (v.Name == "q")
                        {
                            continue;
                        }
                        // set all discrete variables to have constant (0) dynamics
                        if (v.UpdateType == Variable.VarUpdateType.discrete)
                        {
                            spec += v.Name + "_" + i.ToString() + "' == 0 & ";
                        }
                    }

                    if (spec.Length != lbefore)
                    {
                        spec = spec.Substring(0, spec.Length - 3);
                    }
                    else
                    {
                        spec += " True ";
                    }
                    spec += " }" + newline;

                    if (l.Transitions.Count > 0)
                    {
                        foreach (var t in l.Transitions)
                        {
                            // todo: generate label only if transition is not named
                            foreach (var ns in t.NextStates)
                            {
                                // generate sync label
                                spec += "\t when ";
                                if (t.Guard == null && (t.UGuard == null || (t.UGuard != null && N < 2)) && l.Invariant == null && l.Stop == null)
                                {
                                    spec += " true ";
                                }
                                else
                                {
                                    //System.Console.WriteLine("GUARD NAME: " + t.Guard);
                                    //System.Console.WriteLine("GUARD NULL: " + (t.Guard == null));
                                    //System.Console.WriteLine("UGUARD NAME: " + t.UGuard);
                                    //System.Console.WriteLine("UGUARD NULL: " + (t.UGuard == null));
                                    if (t.Guard != null)
                                    {
                                        Expr tmpt = t.Guard;
                                        Expr indexConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);
                                        tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                        tmp = Controller.Instance.Z3.ToStringFormatted(tmpt, outmode.MODE_PHAVER, true); // todo: format appropriately

                                        bool notnull = false;
                                        if (hasPointer)
                                        {
                                            String tmpc = tmp; // copy
                                            for (uint j = 1; j <= N; j++)
                                            {
                                                if (i != j)
                                                {
                                                    tmp = tmpc;
                                                    foreach (var v in h.Variables.Union(h.Parent.Variables))
                                                    {
                                                        if (v.Type == Variable.VarType.index)
                                                        {
                                                            if (tmp.Contains("! (" + v.Name + "[" + i + "] == 0)") || tmp.Contains("! (" + v.Name + " != i)") || tmp.Contains("! (" + v.Name + " == 0)"))
                                                            {
                                                                if (!notnull)
                                                                {
                                                                    spec += "("; // add on first only
                                                                }
                                                                notnull = true; // true for any => true for all

                                                                // for global pointer
                                                                tmp = tmp.Replace("[" + v.Name + "]", "_" + j);
                                                                tmp += " & " + v.Name + " == " + j;

                                                                // for local pointer
                                                                //tmp = tmp.Replace("[" + v.Name + "[" + i + "]]", "_" + j); // replace p[i] with j's actually index, e.g., x[p[i]] -> x_j /\ p[i] = j
                                                                //tmp += " & " + v.Name + "[" + i + "] == " + j;
                                                            }/*
                                                            else
                                                            {
                                                                //tmp = tmp.Replace("[" + v.Name + "[" + i + "]]", "_" + j); // replace p[i] with j's actually index, e.g., x[p[i]] -> x_j /\ p[i] = j
                                                                tmp = tmp.Replace("[" + v.Name + "]", "_" + j);
                                                                tmp += " & " + v.Name + " == " + j;
                                                                notnull = true;
                                                            }*/
                                                        }
                                                    }
                                                    tmp = tmp.Replace("[i]", "_" + i.ToString());
                                                    tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                                    if (notnull)
                                                    {
                                                        spec += "(" + tmp + ")";
                                                        spec += " | ";
                                                    }
                                                }
                                            }
                                            if (notnull)
                                            {
                                                spec = spec.Substring(0, spec.Length - " | ".Length); // remove last or
                                                spec += ")";
                                            }
                                            else
                                            {
                                                tmp = tmp.Replace("[i]", "_" + i.ToString());
                                                tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                                spec += tmp;
                                            }
                                        }
                                        else
                                        {
                                            tmp = tmp.Replace("[i]", "_" + i.ToString());
                                            tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                            spec += tmp;
                                        }
                                        spec += " & ";

                                        
                                    }
                                    if (l.Invariant != null)
                                    {
                                        Expr tmpt = l.Invariant;
                                        Expr indexConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);
                                        tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                        tmp = Controller.Instance.Z3.ToStringFormatted(tmpt, outmode.MODE_PHAVER, true); // todo: format appropriately
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        spec += tmp;
                                        spec += " & ";
                                    }

                                    if (t.UGuard != null & N >= 2)
                                    {
                                        Expr indexConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);

                                        tmp = "";
                                        for (uint j = 1; j <= N; j++)
                                        {
                                            if (i != j)
                                            {
                                                Expr tmpt = Controller.Instance.Z3.copyExpr(t.UGuard);
                                                Expr jIndexConst = Controller.Instance.Z3.MkNumeral(j, Controller.Instance.IndexType);
                                                tmpt = tmpt.Substitute(Controller.Instance.Indices["j"], jIndexConst); // replace j by j value
                                                tmp += "(" + Controller.Instance.Z3.ToStringFormatted(tmpt, outmode.MODE_PHAVER, true) + ")";

                                                //System.Console.WriteLine("UGUARD BEFORE CHANGE (expr): " + tmpt);
                                                //System.Console.WriteLine("UGUARD BEFORE CHANGE (str ): " + tmp);

                                                if (hasPointer)
                                                {
                                                    foreach (var v in h.Variables)
                                                    {
                                                        if (v.Type == Variable.VarType.index)
                                                        {
                                                            tmp = tmp.Replace("[" + v.Name + "[" + i.ToString() + "]]", "_" + j.ToString() + " & " + v.Name + "[" + i.ToString() + "] == " + j); // replace p[i] with j's actually index, e.g., x[p[i]] -> x_j /\ p[i] = j
                                                        }
                                                    }
                                                }

                                                tmp = tmp.Replace("[j]", "_" + j.ToString());
                                                tmp = tmp.Replace("[" + j.ToString() + "]", "_" + j.ToString());

                                                tmp += " & ";
                                            }
                                        }
                                        if (tmp.Length > 0) // loop ran at least once with i != j
                                        {
                                            tmp = tmp.Substring(0, tmp.Length - " & ".Length); // remove and
                                        }
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        spec += tmp;
                                        spec += " & ";
                                    }
                                    /*
                                    if (hasPointer)
                                    {
                                        Expr indexConst = z3.MkNumeral(i, Controller.Instance.IndexType);

                                        tmp = "";
                                        for (uint j = 1; j <= N; j++)
                                        {
                                            //if (i != j) // TODO: exclude self? maybe... in general i guess a pointer p_i could be equal to i, we don't exclude this
                                            //{
                                                Expr tmpt = t.UGuard;
                                                Expr jIndexConst = z3.MkNumeral(j, Controller.Instance.IndexType);
                                                tmpt = tmpt.Substitute(Controller.Instance.Indices["j"], jIndexConst); // replace j by j value
                                                tmp += "(" + z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true) + ")"; // todo: format appropriately
                                                tmp = tmp.Replace("[j]", "_" + j.ToString());
                                                tmp = tmp.Replace("[" + j.ToString() + "]", "_" + j.ToString());
                                                tmp += " & ";
                                            //}
                                        }
                                        if (tmp.Length > 0) // loop ran at least once with i != j
                                        {
                                            tmp = tmp.Substring(0, tmp.Length - " & ".Length); // remove and
                                        }
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        //spec += tmp;
                                        //spec += " & ";
                                    }*/

                                    // phaver semantics differ: just ensure that the invariant contains the negation of the stopping condition
                                    // if we DON'T do this, phaver will do weird stuff on invariants, e.g., it will allow an invariant to go UP TO the value, let it take the transition, and still remain in the state, which differs from our semantics
                                    /*if (l.Stop != null)
                                    {
                                        Expr tmpt = l.Stop;
                                        Expr indexConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);
                                        tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                        tmp = "!(" + Controller.Instance.Z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver) + ")"; // todo: format appropriately
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        spec += tmp + " & ";
                                    }*/
                                    spec = spec.Substring(0, spec.Length - " & ".Length);
                                }

                                string synclab = l.Label + ns.Label + i.ToString(); // unique label for all

                                if (globalSyncLabelsToResetGlobals.ContainsKey(synclab)) // already added this label, add a counter to end of label
                                {
                                    synclab += globalSyncLabelsToResetGlobals.Keys.Count(
                                        delegate(String s)
                                        {
                                            return s == synclab;
                                        }).ToString();
                                }

                                spec += " sync " + synclab + " ";
                                if (t.Reset != null)
                                {
                                    Expr tmpt = t.Reset;
                                    Expr indexConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);
                                    tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                    tmp = Controller.Instance.Z3.ToStringFormatted(tmpt, outmode.MODE_PHAVER); // todo: format appropriately
                                    tmp = tmp.Replace("[i]", "_" + i.ToString());
                                    tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                    IList<Variable> globals = new List<Variable>();
                                    IList<Variable> locals = new List<Variable>();

                                    // TODO: REFACTOR NEXT TO TRANSITION CONSTRUCTOR AND ADD A LIST OF LOCAL/GLOBAL VARIABLE NAMES RESET IN THAT TRANSITION
                                    // find globals reset in t.Reset
                                    foreach (var v in this.Parent.Variables)
                                    {
                                        if (Controller.Instance.Z3.findTerm(t.Reset, Controller.Instance.GlobalVariablesPrimed[v.Name], true)) // todo: add accessor in this.Variables for the expression...
                                        {
                                            globalSyncLabels.Add(synclab);
                                            continue;
                                        }
                                        else
                                        {
                                            globals.Add(v); // set identity
                                        }
                                    }
                                    if (!globalSyncLabelsToResetGlobals.ContainsKey(synclab))
                                    {
                                        globalSyncLabelsToResetGlobals.Add(synclab, globals); // add variables for identity
                                    }
                                    // find locals reset in t.Reset
                                    foreach (Variable v in h.Variables.Where(vtmp => vtmp.Name != "q"))
                                    {
                                        if (Controller.Instance.Z3.findTerm(t.Reset, Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>(v.Name + Controller.PRIME_SUFFIX, "i")], true)) // todo: add accessor in this.Variables for the expression...
                                        {
                                            continue;
                                        }
                                        else
                                        {
                                            locals.Add(v);
                                        }
                                    }

                                    string id = makePhaverIdentity(globals, locals, i); // add identity resets for all variables not actually reset;
                                    if (id.Length > 0)
                                    {
                                        tmp += " & " + id;
                                    }
                                    spec += " do {" + tmp + " } ";
                                }
                                else // if no reset, set all identities
                                {
                                    spec += " do {" + makePhaverIdentity(this.Parent.Variables, h.Variables.Where(vtmp => vtmp.Name != "q"), i) + "} ";
                                } // end reset
                                spec += " goto " + ns.Label + out_endline + newline;
                            }
                        }

                        // add self-loop (tau) transition; must have identity on all local variables (or it will introduce conservative non-determinism, which may lead to violation of properties)
                        spec += "\t when true sync tau do {" + makePhaverIdentity(this.Parent.Variables, h.Variables.Where(vtmp => vtmp.Name != "q"), i) + "} goto " + l.Label + ";" + newline;
                    }
                    else
                    {
                        spec += " ;" + newline;
                    }
                }

                //todo: initially idle & true;
                spec += newline + "initially ";

                foreach (var l in h.Locations)
                {
                    if (l.Initial)
                    {
                        spec += l.Label + " & "; // todo: assumes only one initial location
                    }
                }


                /*if (Controller.Instance.IndexedVariables.Count == 0)
                {
                    tmp = "True";
                }
                else
                {
                    Expr tmpi = h.Initial;
                    Expr iConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);
                    tmpi = tmpi.Substitute(Controller.Instance.Indices["i"], iConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)

                    // todo: huge hack
                    while (tmpi.ASTKind != Z3_ast_kind.Z3_QUANTIFIER_AST && tmpi.NumArgs > 0)
                    {
                        tmpi = tmpi.Args[0];
                    }
                    if (tmpi.ASTKind == Z3_ast_kind.Z3_QUANTIFIER_AST)
                    {
                        tmpi = ((Quantifier)tmpi).Body;
                    }
                    if (tmpi.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_IMPLIES || tmpi.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_OR) // may have simplified implies to not or form
                    {
                        tmpi = tmpi.Args[1];
                    }

                    tmp = Controller.Instance.Z3.ToStringFormatted(tmpi, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                    tmp = tmp.Replace("[i]", "_" + i.ToString());
                    tmp = tmp.Replace("[#0]", "_" + i.ToString()); // z3 3.2 format
                    tmp = tmp.Replace("[(:var 0)]", "_" + i.ToString()); // z3 4.0 format
                     

                }*/
                spec += this.makeInitialString(true).Replace("[i]", "_" + i.ToString());

                // STARL STUFF
                //spec += "x_" + i + " >= " + (x0 - delta_init) + " & x_" + i + " <= " + (x0 + delta_init) + " & y_" + i + " >= " + (y0 - delta_init) + " & y_" + i + " <= " + (y0 + delta_init);

                spec += ";" + newline + newline;

                // todo next: generalize
                //spec += " rem & True;" + newline + newline;
                spec += "end" + newline + newline;
            }

            // create global/shared variable automaton (need to do after local automaton creation to get appropriate sync labels)
            if (this.Parent.Variables.Count > 0)
            {
                spec += out_automaton + " global" + newline;

                spec += out_var_contr + " " + out_separator + " ";
                foreach (var v in this.Parent.Variables) // globals (controlled by global automaton)
                {
                    spec += v.Name + ",";
                }
                spec = spec.Substring(0, spec.Length - 1) + out_endline + newline;

                spec += "synclabs: tau,";

                globalSyncLabels = globalSyncLabels.Distinct().ToList(); // remove duplicates
                foreach (var v in globalSyncLabels)
                {
                    spec += v + ",";
                }
                spec = spec.Substring(0, spec.Length - 1); // strip last comma
                spec += ";" + newline;

                spec += "loc default: while True wait { ";

                foreach (var v in this.Parent.Variables)
                {
                    if (v.UpdateType == Variable.VarUpdateType.discrete)
                    {
                        spec += v.Name + "' == 0 & ";
                    }
                    else
                    {
                        // todo: timed vs. rect
                        spec += v.Name + "' == " + "1" + " & ";
                    }
                }
                spec = spec.Substring(0, spec.Length - 3) + "}" + newline;

                spec += "\t when True sync tau do { " + makePhaverIdentity(this.Parent.Variables, new List<Variable>(), 0) + " } goto default;" + newline; // note identity here over globals only (e.g., g' == g, no x[i]' == x[i])

                foreach (var v in globalSyncLabels)
                {
                    string id = makePhaverIdentity(globalSyncLabelsToResetGlobals[v], new List<Variable>(), 0);
                    spec += "\t when True sync " + v + " do { " + (id.Length > 0 ? id : "true") + " } goto default;" + newline; // note identity here (e.g., g' == g)
                }
                spec += newline;

                // TODO: for each synchronization label (action) of the local automata, if they modify a global variable x, add a sync label for that local action
                //       ALSO: if this action DOES NOT modify some other variables, set identity here
                //       E.g.: if action a modifies x, but not y, then reset should be y' == y, with no constraint on x' (or copy the reset if its not over the local variables of A_i making the move, i.e., if x' == 0, set it)

                //spec += "initially $ & True;" + newline + newline;

                //Expr tmpi = h.Initial;
                //tmpi = tmpi.Args[0].Args[1]; // assumes (forall i ...) and GLOBAL
                //String gitmp = Controller.Instance.Z3.ToStringFormatted(tmpi, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                String gitmp = this.makeInitialString(false);
                spec += "initially default & " + gitmp + ";" + newline + newline;

                spec += "end" + newline + newline;
            }

            spec += "sys = ";
            if (this.Parent.Variables.Count > 0)
            {
                spec += " global & ";
            }

            for (int i = 1; i <= N; i++)
            {
                spec += " agent" + i.ToString() + " & ";
            }
            spec = spec.Substring(0, spec.Length - 3);
            spec += ";" + newline + newline;
            spec += "sys.print(\"" + output_path + "system/" + fnall + ".csys" + "\", 0);" + newline;

            if (newInitial.Length > 0)
            {
                spec += "newinit = sys.{" + newInitial + "};" + newline;
                spec += "sys.initial_states(newinit);" + newline;
                spec += "sys_init = sys.initial_states;" + newline;
                spec += "sys_init.print(\"" + output_path + "system/" + fnall + "_Iteration=" + iteration + ".init" + "\", 0);" + newline;
            }

            spec += "reg = sys.reachable;" + newline;

            spec += "reg.print(\"" + output_path + "reach/" + fnall + ".reach" + "\", 0);" + newline;

            spec += "reg.print(\"" + output_path + "reach/" + fnall + "_Iteration=" + iteration + ".reach" + "\", 0);" + newline;

            string globalNames = ","; // start with comma
            foreach (var v in this.Parent.Variables)
            {
                globalNames += v.Name + ",";
            }
            globalNames = globalNames.Substring(0, globalNames.Length - 1); // note length always > 0 since initially comma (even if var empty): remove last ,

            for (int i = 1; i <= N; i++)
            {
                for (int j = 1; j <= N; j++)
                {
                    if (j == i && j != 1)
                    {
                        continue;
                    }

                    string ij = i.ToString() + j.ToString();
                    /*spec += "regm" + ij + " = reg;" + newline;
                    if (j == 1)
                    {
                        spec += "regm" + ij + ".project_to(x_" + i.ToString() + globalNames + ");" + newline;
                    }
                    else
                    {
                        spec += "regm" + ij + ".project_to(x_" + i.ToString() + ",x_" + j.ToString() + globalNames + ");" + newline;
                    }
                    spec += "regm" + ij + ".print(\"" + h.Name + "_ii_reach_N" + Controller.Instance.IndexNValue + "projected" + ij + "\", 0);" + newline;
                     */
                }
            }

            //spec += "reg.print(\"" + h.Name + "_ii_reach_N" + Controller.Instance.IndexNValue + "\", 0);" + newline;

            /* STARL
            for (int i = 1; i <= N; i++)
            {
                spec += "reg" + i + " = reg;" + newline;
                spec += "reg" + i + ".project_to(x_" + i + "," + "y_" + i + ");" + newline;
                spec += "reg" + i + ".print(\"ii_reach_poly_N" + Controller.Instance.IndexNValue + "_" + i + "\", 2);" + newline;
            }*/

            //spec += "forbidden = sys.{};" + newline;
            // for fischer / mutual exclusion algorithms

            spec += "/*" + newline;
            spec += "forbidden = sys.{";
            for (uint i = 1; i <= N; i++)
            {
                for (uint j = i + 1; j <= N; j++)
                {
                    spec += "$~" + makeBadString("cs", i, j, N) + " & True," + newline; // TODO: set a bad bit on states in input file?
                }
            }
            spec = spec.Substring(0, spec.Length - 2) + "};" + newline;

            /*
             * forbidden=sys.{
                $~CS~CS~$~$~$ & True ,
                $~$~CS~CS~$~$ & True ,
                $~$~$~CS~CS~$ & True ,
                $~$~$~$~CS~CS & True 
                };
             */

            spec += "reg.intersection_assign(forbidden);" + newline;
            spec += "echo \"\";" + newline;
            spec += "echo \"Reachable forbidden states:\";" + newline;
            //spec += "reg.print(\"" + h.Name + "_ii_reach_bad\", 0);" + newline;
            spec += "reg.print(\"" + output_path + "reach/" + h.Name + "_N=" + Controller.Instance.IndexNValue + ".reach_bad" + "\", 0);" + newline;
            spec += "echo \"\";" + newline;
            spec += "echo \"Reachable forbidden states empty?\";" + newline;
            spec += "reg.is_empty;" + newline;
            spec += "*/" + newline;


            return spec;
        }

        /**
         * Return phaver identity for tau transitions
         */
        String makePhaverIdentity(IList<Variable> globals, IEnumerable<Variable> locals, int id)
        {
            String identity = "";

            foreach (var v in globals)
            {
                identity += v.Name + "' == " + v.Name + " & ";
            }

            foreach (var v in locals)
            {
                identity += v.Name + "_" + id + "' == " + v.Name + "_" + id + " & ";
            }
            if (identity.Length > 3)
            {
                identity = identity.Substring(0, identity.Length - 3); // remove last " & " added
            }
            return identity;
        }

        public String makeInitialString(bool indexed)
        {
            String init = "";
            foreach (var v in this.Parent.Variables)
            {
                init += Controller.Instance.Z3.ToStringFormatted(v.Initially, outmode.MODE_PHAVER) + " & ";
            }
            if (indexed)
            {
                foreach (var v in this.Variables)
                {
                    if (v.Name.Equals("q", StringComparison.CurrentCultureIgnoreCase))
                    {
                        continue;
                    }
                    init += Controller.Instance.Z3.ToStringFormatted(v.Initially, outmode.MODE_PHAVER) + " & ";
                }
            }
            if (init.Length == 0)
            {
                init = " True ";
            }
            else
            {
                init = init.Substring(0, init.Length - 3); // remove last " & " added
            }
            return init;
        }

        public Expr makeInitialBmcSymmetric()
        {
            List<BoolExpr> initList = new List<BoolExpr>();

            foreach (var v in this.Parent.Variables)
            {
                initList.Add((BoolExpr)v.Initially);
            }

            // make initial condition expression for indexed variables
            List<BoolExpr> qinit = new List<BoolExpr>();
            foreach (var l in this.Locations)
            {
                if (l.Initial)
                {
                    qinit.Add((BoolExpr)l.StatePredicate);
                }
            }
            if (qinit.Count == 1)
            {
                initList.Add(qinit.First());
            }
            else if (qinit.Count > 1)
            {
                initList.Add(Controller.Instance.Z3.MkOr(qinit.ToArray()));
            }
            else
            {
                throw new Exception("ERROR: bad initial states");
            }

            foreach (var v in this.Variables)
            {
                if (v.Name.Equals("q", StringComparison.CurrentCultureIgnoreCase))
                {
                    continue;
                }
                initList.Add((BoolExpr)v.Initially);
            }
            return Controller.Instance.Z3.MkAnd(initList.ToArray());
        }

        public Expr makeInitialBmc(uint N)
        {
            List<BoolExpr> initList = new List<BoolExpr>();

            foreach (var v in this.Parent.Variables)
            {
                initList.Add((BoolExpr)v.Initially);
            }

            // make initial condition expression for indexed variables
            for (uint i = 1; i <= N; i++)
            {

                BoolExpr qinit = Controller.Instance.Z3.MkFalse();
                foreach (var l in this.Locations)
                {
                    if (l.Initial)
                    {
                        qinit = Controller.Instance.Z3.MkOr(qinit, (BoolExpr)l.StatePredicate.Substitute(Controller.Instance.Indices["i"], Controller.Instance.Z3.MkInt(i)));
                    }
                }
                initList.Add(qinit); // TODO: CHECK IF ADDED CORRECTLY HERE

                foreach (var v in this.Variables)
                {
                    if (v.Name.Equals("q", StringComparison.CurrentCultureIgnoreCase))
                    {
                        continue;
                    }
                    initList.Add((BoolExpr)v.Initially.Substitute(Controller.Instance.Indices["i"], Controller.Instance.Z3.MkInt(i)));
                }
            }
            return Controller.Instance.Z3.MkAnd(initList.ToArray());
        }

        String toPHaverSyntax(String s)
        {
            return "";
        }

        String makeBadString(String statename, uint i, uint j, uint N)
        {
            String s = "";
            for (uint ti = 1; ti <= N; ti++)
            {
                if (ti == i || ti == j)
                {
                    s += statename + "~";
                }
                else
                {
                    s += "$~";
                }
            }
            s = s.Substring(0, s.Length - 1);
            return s;
        }
    }
}
