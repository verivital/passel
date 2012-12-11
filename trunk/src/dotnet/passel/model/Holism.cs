using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;
using passel.controller.smt;
using passel.controller.smt.z3;

namespace passel.model
{
    /**
     * Complete system specification (couldn't name it system for obvious reasons, e.g., name conflicts)
     * Contains property specifications, global variables, and indexed hybrid automata
     */
    public class Holism
    {
        /**
         * Dictionary mapping tuples of <variable name, round, process id> to appropriate expressions (e.g., xk_i, where x is variable name, k is round, and i is index)
         */
        public Dictionary<Tuple<String, uint, uint>, Expr> ReachValues = new Dictionary<Tuple<string, uint, uint>, Expr>();

        /**
         * Hybrid automata
         */
        private List<ConcreteHybridAutomaton> _has;

        private Z3Wrapper z3 = Controller.Instance.Z3;

        public List<Transition> Transitions = new List<Transition>();

        /**
         * Properties to be checked
         */
        protected List<Property> _properties;

        /**
         * Global variables
         */
        protected List<Variable> _variables = new List<Variable>();

        /**
         * Gettor for global variables
         */
        public List<Variable> Variables
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
         * Default Constructor
         */
        public Holism()
        {
            this._properties = new List<Property>();
            this._has = new List<ConcreteHybridAutomaton>();
        }

        /**
         * Accessor for hybrid automata
         */
        public List<ConcreteHybridAutomaton> HybridAutomata
        {
            get { return this._has; }
            set { this._has = value; }
        }

        /**
         * Accessor for properties
         */
        public List<Property> Properties
        {
            get { return this._properties; }
            set { this._properties = value; }
        }

        /**
         * Add a transition to the list of global transitions
         */
        public void addTransition(Transition t)
        {
            if (this.Transitions == null)
            {
                this.Transitions = new List<Transition>();
            }
            this.Transitions.Add(t);
        }

        /**
         * Add a hybrid automaton to the list of automata
         */
        public void addHybridAutomaton(ConcreteHybridAutomaton ha)
        {
            if (this._has == null)
            {
                this._has = new List<ConcreteHybridAutomaton>();
            }
            this._has.Add(ha);
        }

        /**
         * Remove duplicate properties
         */
        public void removeDuplicateProperties()
        {
            this.Properties = this.Properties.Distinct().ToList();

            // todo: use distinct as in previous line combined with comparer that looks at Property.Formula
            // remove duplicates by formulas
            int c = this.Properties.Count;
            for (int i = 0; i < c; i++)
            {
                for (int j = 1; j < c; j++)
                {
                    if (i == j || i == this.Properties.Count || j == this.Properties.Count)
                    {
                        continue;
                    }

                    // try proving them equal
                    Controller.Instance.Z3.slvr.Push(); // save original context
                    BoolExpr p = Controller.Instance.Z3.MkIff((BoolExpr)this.Properties[i].Formula, (BoolExpr)this.Properties[j].Formula); // prop_i = prop_j
                    Model m;
                    Expr[] core;
                    String stat;

                    if (this.Properties[i].Formula.Equals(this.Properties[j].Formula) || Controller.Instance.Z3.proveTerm(p, out m, out core, out stat)) // short-circuit, don't prove them equal if we can do the simple check
                    {
                        System.Console.WriteLine("REMOVING PROPERTY, DUPLICATE\n\r");
                        this.Properties.RemoveAt(j);
                        c = this.Properties.Count; // update count
                    }
                    Controller.Instance.Z3.slvr.Pop(); // restore original context
                }
            }
        }

        /**
         * TODO: refactoring
         * 
         * Break the property loop out of the following
         * 
         * Make a function that checks a property across every transition (not specific to inductive invariants)
         * 
         * 
         */


        /**
         * Assume each property is a candidate inductive invariant, then we need to check each transition with respect to it
         */
        public void checkInductiveInvariants()
        {
            if (this._has == null)
            {
                return;
            }
            ConcreteHybridAutomaton h = this._has.First(); // assume only one ha
            bool iinv = true;
            bool inv = true;
            bool subpart = false;
            bool restart = true;
            int proveCount = 0;
            int property_idx = 0;
            int proofPass = -1;
            int loops = 0;

            //z3.Assumptions.RemoveAll(a => a.IsQuantifier);

            this.z3.slvr.Assert(this.z3.Assumptions.ToArray()); // assert all the data-type assumptions
            this.z3.slvr.Assert(this.z3.AssumptionsUniversal.ToArray()); // assert all the data-type assumptions
            

            System.Console.WriteLine("Attempting to prove the following properties as inductive invariants: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property pi in this.Properties)
            {
                System.Console.WriteLine(pi.Formula.ToString() + "\n\r");

                System.Console.WriteLine(pi.Post.ToString() + "\n\r");
            }

            Property p = null;

            while (true)
            { 
                if (!restart && property_idx == this.Properties.Count) // && this.Properties[property_idx].Status != StatusTypes.toProcess)
                {
                    break;
                }

                //if (restart)
                if (restart && property_idx == this.Properties.Count || loops <= 0) // only restart after we go through the whole list of properties (worst case behavior is the same, but on average this seems better)
                {
                    p = null;
                    proofPass++;
                    foreach (var ptmp in this.Properties)
                    {
                        if (ptmp.Status == StatusTypes.disproved)
                        {
                            ptmp.QuantInstantiations = 0;
                            ptmp.Status = StatusTypes.toProcess;
                            ptmp.InductiveInvariants = new List<Expr>(); // need to reset this as well

                            // clear out counterexample models
                            foreach (var v in ptmp.Counterexamples)
                            {
                                v.Model = null;
                            }
                            ptmp.Counterexamples = new List<Counterexample>();
                        }
                    }

                    System.Console.WriteLine("\n\rProperties proved and used as assumption lemmas: \n\r\n\r");
                    foreach (var ptmp in this.Properties)
                    {
                        if (ptmp.Status == StatusTypes.inductiveInvariant)
                        {
                            //System.Console.WriteLine(ptmp.Formula.ToString() + "\n\r\n\r");
                        }

                        if (ptmp.Status == StatusTypes.inductive)
                        {
                            foreach (var pt in ptmp.InductiveInvariants)
                            {
                                //System.Console.WriteLine(pt.ToString() + "\n\r\n\r");
                            }
                        }
                    }

                    z3.slvr.Push(); // PUSH1_POP1
                    z3.slvr.Check();
                    Expr[] a = z3.slvr.Assertions;
                    System.Console.WriteLine("\n\r\n\rASSUMPTIONS: \n\r" + z3.ExprArrayToString(a) + "\n\r\n\r");

                    /*
                    Microsoft.Z3.Tactic t = z3.MkTactic();
                    Microsoft.Z3.Goal g = z3.MkGoal();
                    g.Assert(z3.slvr.Assertions);
                    t.Apply(g);
                     */


                    Status ca = z3.slvr.Check();
                    if (ca == Status.UNKNOWN || ca == Status.UNSATISFIABLE)
                    {
                        //throw new Exception("ERROR: basic assumptions on data types, indices, etc. cannot be satisfied!");
                    }
                    try
                    {
                        if (z3.slvr.Model != null)
                        {
                            System.Console.WriteLine("Model for basic assumptions: \n\r\n\r");
                            System.Console.WriteLine(z3.slvr.Model.ToString());
                        }
                        if (z3.slvr.UnsatCore != null)
                        {
                            Console.WriteLine("Unsat core:\n\r");
                            foreach (Expr c in z3.slvr.UnsatCore)
                            {
                                Console.WriteLine("{0}", c);
                            }
                        }
                    }
                    catch (Exception e)
                    {
                    }
                    z3.slvr.Pop(); // PUSH1_POP1

                    restart = false; // don't do this at every run
                    property_idx = 0; // start back over on the properties
                }

                int QuantInstantiationsLast;
                if (p != null)
                {
                    QuantInstantiationsLast = p.QuantInstantiations; // copy over to do the delta
                }
                else
                {
                    QuantInstantiationsLast = 0;
                }

                p = this._properties[property_idx++]; // increment after read

                if (p.Status == StatusTypes.toProcess)
                {
                    p.InductiveInvariants = new List<Expr>(); // need to reset this as well2
                    p.Status = StatusTypes.unknown;
                }
                else
                {
                    continue;
                }

                // runtime statistics
                Controller.Instance.TimerStats.Reset();
                Controller.Instance.TimerStats.Start();

                proveCount = 0;
                subpart = false;
                iinv = true; // reset invariant shortcircuit var
                inv = true;
                // todo next: switch , Controller.Instance.IndexType
                Expr hidx = z3.MkIntConst("h"); // h is the process making transitions
                List<Transition> tViolate = new List<Transition>(); // list of transitions that violate invariant

                Model model = null;
                Expr[] core = null;

                String tmp_stat;
                // initiation (inductive invariance): if disproved, set as not being inductive invariant
                if (!z3.proveTerm(z3.MkImplies((BoolExpr)h.Initial, (BoolExpr)p.Formula), out model, out core, out tmp_stat, true))
                {
                    System.Console.WriteLine("INITIAL FAIL");
                    inv = false; // actually, perhaps we only check the invariant if we proved the term?
                    iinv = false;
                    p.Status = StatusTypes.disproved;
                    if (core != null)
                    {
                        Console.WriteLine("Unsat core:\n\r");
                        foreach (Expr c in core)
                        {
                            Console.WriteLine("{0}", c);
                        }
                        core = null;
                    }
                }

                //if (iinv)
                if (true)
                {
                    //List<BoolExpr> discreteall = new List<BoolExpr>(); // conjunction of all possible locations for discrete transitions
                    List<BoolExpr> timeall = new List<BoolExpr>(); // conjunction of all possible locations for time transition
                    
                    // global discrete transitions
                    foreach (var t in this.Transitions)
                    {
                        Expr inductiveInvariant = p.Formula;

                        //inductiveInvariant = z3.MkAnd((BoolExpr)inductiveInvariant, (BoolExpr)t.TransitionTermGlobal);
                        Expr hidxinner = z3.MkIntConst("h");
                        Expr transitionTerm = this.makeTransitionTerm(t, null, hidxinner);
                        inductiveInvariant = z3.MkAnd((BoolExpr)inductiveInvariant, (BoolExpr)transitionTerm);

                        // alternative next, get the body and recreate
                        //Quantifier orig = inductiveInvariant.GetQuantifier();
                        //inductiveInvariant = inductiveInvariant.GetQuantifier().Body & z3.MkExists(0, bound.ToArray(), null, locInvariantAnd);
                        //inductiveInvariant = z3.MkForall(orig.Weight, null, orig.Sorts, orig.Names, inductiveInvariant);

                        //if (z3.checkTerm(inductiveInvariant, out model, out core, true))
                        //if (z3.proveTerm(inductiveInvariant, out model, out core, true))
                        if (true)
                        {
                            //z3.checkTerm(inductiveInvariant, out model, out core, true);
                            //Console.WriteLine("\n\r<><><><><> GUARDED MODEL START\n\r\n\r");
                            //Console.WriteLine(inductiveInvariant.ToString() + "\n\r\n\r");
                            //if (z3.slvr.Model != null)
                            //{
                            //    Console.WriteLine(z3.slvr.Model.ToString());
                            //}
                            //Console.WriteLine("\n\r<><><><><> GUARDED MODEL END\n\r\n\r");

                            Expr claim = z3.MkImplies((BoolExpr)inductiveInvariant, (BoolExpr)p.Post);

                            Console.WriteLine("\n\r<><><><><> INDUCTIVE INVARIANT START\n\r\n\r");
                            //Console.WriteLine(claim.ToString() + "\n\r\n\r");
                            //if (z3.slvr.Model != null)
                            //{
                            //    Console.WriteLine(z3.slvr.Model.ToString());
                            //}
                            Console.WriteLine("\n\r<><><><><> INDUCTIVE INVARIANT END\n\r\n\r");

                            //z3.Push();
                            //z3.AssertCnstr(inductiveInvariant);
                            //claim = z3.Simplify(claim);

                            //if (z3.proveTerm(p.Post, out model, out core, out tmp_stat, true))
                            if (z3.proveTerm(claim, out model, out core, out tmp_stat, true))
                            {
                                p.Statistics.Add(tmp_stat);
                                if (core != null)
                                {
                                    Console.WriteLine("Unsat core:\n\r");
                                    foreach (Expr c in core)
                                    {
                                        Console.WriteLine("{0}", c);
                                    }
                                    core = null;
                                }
                                // proved inductive invariant (for this transition)
                                //subpart = true;
                                proveCount++;
                            }
                            else
                            {
                                p.Statistics.Add(tmp_stat);
                                inv = false;
                                iinv = false;
                                tViolate.Add(t);
                                p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claim)); // TODO: fix model generation
                                //p.Counterexamples.Add(new Counterexample(null, claim)); // TODO: fix model generation
                            }
                            //z3.Pop();

                            p.addInductiveInvariant(claim);
                        }

                    } // end global discrete actions

                    foreach (ConcreteLocation l in h.Locations)
                    {
                        foreach (var t in l.Transitions)
                        {
                            Expr inductiveInvariant = p.Formula;

                            // todo next: switch index type if not int
                            //Expr hidxinner = z3.MkConst("h", Controller.Instance.IndexType);
                            Expr hidxinner = z3.MkIntConst("h");
                            Expr transitionTerm = this.makeTransitionTerm(t, l, hidxinner);
                            //Expr transitionTerm = t.TransitionTerm;

                            List<Expr> bound = new List<Expr>();
                            //hidx = z3.MkConst("h", Controller.Instance.IndexType);
                            hidx = z3.MkIntConst("h");
                            bound.Add(hidx);

                            inductiveInvariant = z3.MkAnd((BoolExpr)inductiveInvariant, z3.MkExists(bound.ToArray(), transitionTerm)); // TODO: WAS AND, TRYING IMPLIES
                            //inductiveInvariant = z3.MkImplies((BoolExpr)inductiveInvariant, z3.MkExists(bound.ToArray(), transitionTerm));

                            z3.slvr.Push();
                            //z3.slvr.Assert((BoolExpr)inductiveInvariant);
                            //z3.slvr.Assert(z3.MkExists(bound.ToArray(), transitionTerm));

                            // alternative next, get the body and recreate
                            //Quantifier orig = inductiveInvariant.GetQuantifier();
                            //inductiveInvariant = inductiveInvariant.GetQuantifier().Body & z3.MkExists(0, bound.ToArray(), null, locInvariantAnd);
                            //inductiveInvariant = z3.MkForall(orig.Weight, null, orig.Sorts, orig.Names, inductiveInvariant);

                            //if (z3.checkTerm(inductiveInvariant, out model, out core, true))
                            //if (z3.proveTerm(inductiveInvariant, out model, out core, true))
                            if (true)
                            {
                                /*
                                Boolean res = z3.checkTerm(inductiveInvariant, out model, out core, true);
                                res = res;
                                if (res)
                                {
                                    bool tenabled = res; // omg...
                                    tenabled = tenabled;
                                }*/

                                z3.slvr.Assert((BoolExpr)inductiveInvariant);

                                /*
                                Goal g = z3.MkGoal(true, true, false);
                                g.Assert(z3.slvr.Assertions);
                                Tactic tac = z3.MkTactic("qe");
                                ApplyResult a;
                                a = tac.Apply(g);
                                tac = z3.MkTactic("smt");
                                a = tac.Apply(g);
                                a = a;
                                 

                                //z3.checkTerm(z3.MkTrue(), out model, out core, true);
                                Status ao = Status.UNKNOWN;
                                ao = z3.slvr.Check();
                                switch (ao)
                                {
                                    case Status.SATISFIABLE:
                                        Console.Write("guard sat");
                                        break;
                                    case Status.UNKNOWN:
                                        Console.Write("guard unknown");
                                        break;
                                    case Status.UNSATISFIABLE:
                                        Console.Write("guard unsat");
                                        break;
                                }
                                String unsatcore = z3.ExprArrayToString(core);
                                Console.WriteLine("core: " + unsatcore + "\n\r\n\r");
                                Double asdf = 5;
                                asdf = 3;
                                asdf = asdf + 1;
                                Console.WriteLine("\n\r<><><><><> GUARDED MODEL START\n\r\n\r");
                                Console.WriteLine(inductiveInvariant.ToString() + "\n\r\n\r");
                                //if (z3.slvr.Model != null)
                                //{
                                //    Console.WriteLine(z3.slvr.Model.ToString());
                                //}
                                Console.WriteLine("\n\r<><><><><> GUARDED MODEL END\n\r\n\r");
                                 */

                                /*
                                // ranking function synthesis
                                Expr eps_rank = z3.MkConst("eps_rank", Controller.Instance.RealType);
                                if (!Controller.Instance.ExistentialConstants.ContainsKey("eps_rank"))
                                {
                                    Controller.Instance.ExistentialConstants.Add("eps_rank", eps_rank);
                                }*/

                                //List<BoolExpr> ts = new List<BoolExpr>();
                                //ts.Add((BoolExpr)p.Post); // invariant
                                //ts.Add( z3.MkGe((ArithExpr)p.FormulaRankLhs, z3.MkAdd((ArithExpr)p.FormulaRankRhs, (ArithExpr)eps_rank))); // ranking
                                //ts.Add( z3.MkGe(z3.MkSub((ArithExpr)p.FormulaRankLhs, (ArithExpr)p.FormulaRankRhs), Controller.Instance.RealZero)); // unaffecting (todo: check i vs j indexing)
                                //ts.Add( z3.MkGe((ArithExpr)p.FormulaRankLhs, Controller.Instance.RealZero)); // bounded (todo: check i vs j indexing)
                                //Expr claim = z3.MkImplies(z3.MkAnd((BoolExpr)inductiveInvariant, z3.MkGt((ArithExpr)eps_rank, Controller.Instance.RealZero)), z3.MkAnd(ts.ToArray())); // todo: was just p.Post for inductive invariants
                                Expr claim = z3.MkImplies((BoolExpr)inductiveInvariant, (BoolExpr)p.Post); // just inductive invariants
                                

                                Console.WriteLine("\n\r<><><><><> INDUCTIVE INVARIANT START\n\r\n\r");
                                //Console.WriteLine(claim.ToString() + "\n\r\n\r");
                                //if (z3.slvr.Model != null)
                                //{
                                //    Console.WriteLine(z3.slvr.Model.ToString());
                                //}
                                Console.WriteLine("\n\r<><><><><> INDUCTIVE INVARIANT END\n\r\n\r");

                                //z3.slvr.Push();
                                //z3.slvr.Assert((BoolExpr)inductiveInvariant);
                                //claim = claim.Simplify();

                                //Console.WriteLine("GENERATED INVARIANT MODEL (may return unknown; note, doesn't need existential over invariant terms, it has this implicitly in the sat formulation)\n\r");
                                // todo next: we can simply check satisfiability to actually get values for the invariant
                                //z3.checkTerm(claim, out model, out core, true);

                                
                                // TODO: the following existential probably has to be uniform across ALL transitions---i.e., the epsilon decrease has to be the same for every transition...? this differs somewhat
                                // from how we can check safety properties by checking each transition separately
                                //claim = z3.MkExists(0, Controller.Instance.ExistentialConstants.Values.ToArray(), null, claim); // todo: only do this for termination properties
                                //discreteall.Add((BoolExpr)claim);

                                //Console.WriteLine("GENERATED INVARIANT MODEL (explicit quantifiers)\n\r");
                                //z3.checkTerm(claim, out model, out core, true);

                                if (z3.proveTerm(p.Post, out model, out core, out tmp_stat, true))
                                //if (z3.proveTerm(claim, out model, out core, out tmp_stat, true))
                                {
                                    p.Statistics.Add(tmp_stat);
                                    if (core != null)
                                    {
                                        Console.WriteLine("Unsat core:\n\r");
                                        foreach (Expr c in core)
                                        {
                                            Console.WriteLine("{0}", c);
                                        }
                                        core = null;
                                    }
                                    // proved inductive invariant (for this transition)
                                    //subpart = true;
                                    proveCount++;
                                }
                                else
                                {
                                    p.Statistics.Add(tmp_stat);
                                    inv = false;
                                    iinv = false;
                                    tViolate.Add(t);
                                    p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claim)); // TODO: FIGURE OUT WHY MODEL GENERATION DOESN'T WORK WHEN USING A TACTIC-BASED SOLVER
                                    //p.Counterexamples.Add(new Counterexample(null, claim)); // TODO: FIGURE OUT WHY MODEL GENERATION DOESN'T WORK WHEN USING A TACTIC-BASED SOLVER
                                }
                                z3.slvr.Pop();

                                p.addInductiveInvariant(claim);
                            }

                        } // end discrete actions


                        // TODO: only check time transition if protocol has at least one continuous variable...

                        // start continuous transition (we add a a part for each location as we iterate over them)
                        //hidx = z3.MkConst("h", Controller.Instance.IndexType); // make fresh
                        hidx = z3.MkIntConst("h");

                        if (l.Flows == null || l.Flows.Count == 0 || l.Flows[0].DynamicsType == Flow.DynamicsTypes.constant) // TODO: CHECK ALL FLOWS, THIS WORKS ONLY FOR ONE VAR
                        {
                            Expr tmpterm = z3.MkImplies((BoolExpr)l.StatePredicate, (BoolExpr)z3.timeNoFlowIdentity(hidx));
                            tmpterm = tmpterm.Substitute(Controller.Instance.Indices["i"], hidx); // replace i by h

                            timeall.Add((BoolExpr)tmpterm);

                            if (timeall.Count != h.Locations.Count) // only continue if nothing in timed list, otherwise if the last location has null flow, the others will also get skipped
                            {
                                continue; // no dynamics (e.g., x' == 0), skip time transition
                            }

                            // todo: this makes the most sense, but should we allow the full generality of having an invariant and stopping condition even when we will have identity for time? (i.e., the stop/inv could force a transition, but it would sort of be illegal...)
                        }

                        Expr timeii = this.makeFlowsAll(h, p.Formula);
                        
                        p.addInductiveInvariant(timeii);

                        //if (z3.checkTerm(timeii, out model, out core, true))
                        //if (z3.proveTerm(inductiveInvariant, out model, out core, true))
                        if (true)
                        {
                            //z3.checkTerm(timeii, out model, out core, true);


                            timeii = z3.MkImplies((BoolExpr)timeii, (BoolExpr)p.Post);

                            //timeii = z3.MkExists(Controller.Instance.ExistentialConstants.Values.ToArray(), timeii); // todo: only do this for termination properties

                            if (z3.proveTerm(timeii, out model, out core, out tmp_stat, true))
                            {
                                p.Statistics.Add(tmp_stat);
                                // proved inductive invariant (for this location of the timed transition)
                                if (core != null)
                                {
                                    Console.WriteLine("Unsat core:\n\r");
                                    foreach (Expr c in core)
                                    {
                                        Console.WriteLine("{0}", c);
                                    }
                                    core = null;
                                }
                                proveCount++;
                            }
                            else
                            {
                                p.Statistics.Add(tmp_stat);
                                inv = false;
                                iinv = false;
                                p.Counterexamples.Add(new Counterexample(z3.slvr.Model, timeii)); // TODO: fix model generation
                                //p.Counterexamples.Add(new Counterexample(null, timeii)); // TODO: fix model generation
                            }
                        }
                    }
                }

                if (proveCount == 0)
                {
                    iinv = false;
                    inv = false;
                }

                // property is not an inductive invariant
                if (!iinv)
                {
                    Console.WriteLine("\n\r\n\rProperty was NOT an inductive invariant!");
                    //Console.WriteLine("Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    Console.WriteLine("\n\r\n\rProperty was an inductive invariant!");
                    //Console.WriteLine("Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.inductiveInvariant;

                    switch (p.Type)
                    {
                        case Property.PropertyType.safety_weak:
                            {
                                //z3.AssertCnstr(z3.MkImplies(p.Formula, p.Post));
                                break;
                            }
                        case Property.PropertyType.safety:
                        case Property.PropertyType.invariant:
                        default:
                            {
                                // assert the property as a lemma
                                //z3.Assumptions.Add((BoolExpr)p.Formula);
                                z3.slvr.Assert((BoolExpr)p.Formula); // TODO: RENABLE

                                //Term simple_ii = z3.MkImplies(p.Formula, formulaPrime);
                                //z3.AssertCnstr(simple_ii);
                                //z3.Assumptions.Add((BoolExpr)p.Post);
                                z3.slvr.Assert((BoolExpr)p.Post); // TODO: REENABLE

                                p.ProvedPass = proofPass;
                                break;
                            }
                    }

                    //z3.AssertCnstr(z3.MkOr(p.InductiveInvariants.ToArray())); // disjunction of all transitions is the transition relation, not conjunction!
                    // also assert the inductive invariant claim since it is strictly stronger than an invariant property (i.e., ii => i, but ii !<= i necessarily)
                }


                // property is not inductive (a property may be inductive without being an inductive invariant, e.g., if only the initial condition check fails)
                if (!inv)
                {
                    Console.WriteLine("\n\r\n\rProperty was NOT inductive!");
                    //Console.WriteLine("Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    // only do this for non-invariants
                    if (!iinv)
                    {
                        Console.WriteLine("\n\r\n\rProperty was inductive!");
                        //Console.WriteLine("Property checked was: \n\r" + p.Formula.ToString());
                        p.Status = StatusTypes.inductive;

                        //z3.AssertCnstr(p.Formula); // probably don't want to assert this, as this would require it to be invariant

                        p.InductiveFormula = z3.MkOr((BoolExpr[])p.InductiveInvariants.ToArray());
                    }
                }
                Controller.Instance.TimerStats.Stop();

                // once we assert a property as a lemma, we go back to all other formulas and attempt to reprove them so that the order of the lemma assertions does not matter
                if (subpart || iinv || inv)
                {
                    restart = true;

                    // edge case if last lemma is disproved
                    if (property_idx == this.Properties.Count)
                    {
                        property_idx = 0;
                    }
                }


                String quantInstStr = p.Statistics[p.Statistics.Count-1];
                //quantInstStr = quantInstStr.Substring(quantInstStr.IndexOf("\nquant instantiations:")).Trim(); // use newline: there is another statistic called "lazy quantifier instantiations:", so we don't want to match that (otherwise get wrong or even negative values)
                //quantInstStr = quantInstStr.Split(':')[1].Split('\n')[0];
                //p.QuantInstantiations = int.Parse(quantInstStr) - QuantInstantiationsLast;
                //
                




                p.Time = Controller.Instance.TimerStats.Elapsed;
                loops++;
            }


            System.Console.WriteLine("\n\r\n\rDISPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property pi in this.Properties)
            {
                if (pi.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine("PROPERTY DISPROVED =====================================================================\n\r");
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r\n\r");

                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r");

                    System.Console.WriteLine("REASONS (counterexample / trace):\n\r");
                    foreach (Counterexample ce in pi.Counterexamples)
                    {
                        if (ce.Model != null)
                        {
                            System.Console.WriteLine("Counterexample model:\n\r");
                            System.Console.WriteLine(ce.Model.ToString());
                            System.Console.WriteLine("\n\r\n\r");
                        }

                        if (ce.Claim != null)
                        {
                            System.Console.WriteLine("Inductive invariant claim:\n\r\n\r");
                            System.Console.WriteLine(ce.Claim.ToString() + "\n\r\n\r");
                            //System.Console.WriteLine("Simplified inductive invariant claim:\n\r\n\r");
                            //System.Console.WriteLine(z3.Simplify(ce.Claim).ToString() + "\n\r\n\r");
                            //System.Console.WriteLine("Negation of inductive invariant claim:\n\r\n\r");
                            //System.Console.WriteLine((!ce.Claim).ToString() + "\n\r\n\r");
                            //System.Console.WriteLine("Simplified negation of inductive invariant claim:\n\r\n\r");
                            //System.Console.WriteLine(z3.Simplify(!ce.Claim).ToString() + "\n\r\n\r");
                        }

                        //if (ce.Transition != null)
                        //{
                        //    System.Console.WriteLine("Counterexample transition:\n\r");
                        //    //System.Console.WriteLine( ce.Transition.t
                        //    System.Console.WriteLine("\n\r\n\r");
                        //}
                    }
                    System.Console.WriteLine("END PROPERTY DISPROVED =====================================================================\n\r\n\r\n\r\n\r");
                }
            }

            /*
            System.Console.WriteLine("DISPROVED INVARIANTS SUMMARY WITH STATISTICS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property pi in this.Properties)
            {
                if (pi.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r\n\r");
                    System.Console.WriteLine("Statistics: \n\r");
                    foreach (var stmp in pi.Statistics)
                    {
                        System.Console.WriteLine(stmp + "\n\r\n\r");
                    }
                }
            }
            
            System.Console.WriteLine("\n\rPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property pi in this.Properties)
            {
                if (pi.Status == StatusTypes.inductiveInvariant)
                {
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r\n\r");
                    System.Console.WriteLine("Statistics: \n\r");
                    foreach (var stmp in pi.Statistics)
                    {
                        System.Console.WriteLine(stmp + "\n\r\n\r");
                    }
                }
            }*/

            /*
            System.Console.WriteLine("\n\rPROVED INDUCTIVE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property pi in this.Properties)
            {
                if (pi.Status == StatusTypes.inductive)
                {
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r\n\r");
                    System.Console.WriteLine("Statistics: \n\r");
                    foreach (var stmp in pi.Statistics)
                    {
                        System.Console.WriteLine(stmp + "\n\r\n\r");
                    }
                }
            }
             */



            System.Console.WriteLine("DISPROVED INVARIANTS SUMMARY WITH SHORT RUNTIME >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            int num_dis = 0;
            foreach (Property pi in this.Properties)
            {
                if (pi.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r\n\r");
                    num_dis++;
                }
            }

            System.Console.WriteLine("\n\rPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            int num_inv = 0;
            foreach (Property pi in this.Properties)
            {
                // TODO: ADD ELEMENT TO PROPERTY PARSER
                if ((pi.ProjectedFrom == null || pi.ProjectedFrom <= 0) && (pi.FormulaStr != null && !pi.FormulaStr.Contains("true") && !pi.FormulaStr.Contains("false"))) // original property
                {
                    Controller.Instance.appendLogEvent("inductive?", Controller.Instance.sysname, pi.FormulaStr + " " + (pi.Status == StatusTypes.inductiveInvariant).ToString());
                }
                    /*
                else
                {
                    Controller.Instance.appendLogEvent("\\phi inductive?", Controller.Instance.sysname, pi.Status.ToString());
                }
                     */



                if (pi.Status == StatusTypes.inductiveInvariant)
                {
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Proof pass: " + pi.ProvedPass.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r\n\r");
                    num_inv++;
                }
            }
            /*
            int num_ind = 0;
            System.Console.WriteLine("\n\rPROVED INDUCTIVE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property pi in this.Properties)
            {
                if (pi.Status == StatusTypes.inductive)
                {
                    System.Console.WriteLine(pi.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r\n\r");
                    num_ind++;
                }
            }*/

            System.Console.WriteLine("\n\rSUMMARY\n\r");
            System.Console.WriteLine("Disproved: " + num_dis.ToString());
            System.Console.WriteLine("Invariant: " + num_inv.ToString());
            //System.Console.WriteLine("Inductive: " + num_ind.ToString());

            /*
            System.Console.WriteLine("\n\rLatex Table\n\r\n\r");
            foreach (Property pi in this.Properties)
            {
                // skip for non-buggy to get the desired properties
                if (pi.Status != StatusTypes.inductiveInvariant)
                {
                    //continue;
                }

                String latex = z3.ToStringFormatted(pi.Formula, controller.smt.z3.Z3Wrapper.PrintFormatMode.latex);
                int qi = pi.QuantInstantiations;
                System.Console.Write(" & $" + latex + "$ & ");
                if (pi.Status == StatusTypes.inductiveInvariant)
                {
                    System.Console.Write("\\tickYes");
                }
                else
                {
                    System.Console.Write("\\tickNo");
                }
                String timeStr = Math.Round(pi.Time.TotalSeconds, 3).ToString();
                System.Console.WriteLine(" & $" + timeStr + "$ & $" + qi.ToString() + "$ \\\\ ");
            }
             */
        }


        public Expr makeFlowsAll(AHybridAutomaton h, Expr prestate, params uint[] paramsList)
        {
            uint k = 0;
            if (paramsList != null && paramsList.Length > 0)
            {
                k = paramsList[0];
            }


            List<BoolExpr> timeall = new List<BoolExpr>();
            Expr timeii = prestate;
            foreach (Location l in h.Locations)
            {
                

                List<BoolExpr> exprlist = new List<BoolExpr>();
                Expr expr = null;
                ArithExpr t1 = (ArithExpr)z3.MkRealConst("t_1"); // existential
                ArithExpr t2 = (ArithExpr)z3.MkRealConst("t_2"); // universal
                ArithExpr delta = (ArithExpr)z3.MkRealConst("delta"); // existential (for rectangular dynamics)

                // add invariant
                if (l.Invariant != null)
                {
                    Expr tmpterm = l.Invariant;

                    // indexed variables
                    foreach (var v in h.Variables)
                    {
                        tmpterm = this.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")], l, t1, t2, delta);
                    }

                    // TODO: NEED TO REASSIGNED tmpterm TO THE INVARIANT (AND STOPPING CONDITION IN THE NEXT ONE)?

                    // global variables
                    foreach (var v in h.Parent.Variables)
                    {
                        tmpterm = this.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.GlobalVariables[v.Name], l, t1, t2, delta);
                    }
                    exprlist.Add((BoolExpr)tmpterm);
                }

                // add stopping condition
                if (l.Stop != null)
                {
                    Expr tmpterm = z3.MkImplies((BoolExpr)l.Stop, z3.MkEq(t1, t2));

                    // indexed variables
                    foreach (var v in h.Variables)
                    {
                        tmpterm = this.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")], l, t1, t2, delta);
                    }

                    // global variables
                    foreach (var v in h.Parent.Variables)
                    {
                        tmpterm = this.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.GlobalVariables[v.Name], l, t1, t2, delta);
                    }
                    exprlist.Add((BoolExpr)tmpterm);
                }

                // do flow afterward, it already has primed variables
                if (l.Flows != null)
                {
                    foreach (Flow f in l.Flows)
                    {
                        switch (f.DynamicsType)
                        {
                            case Flow.DynamicsTypes.constant:
                                {
                                    continue;
                                }
                            case Flow.DynamicsTypes.rectangular:
                                {
                                    Expr flow = f.Value;
                                    flow = f.Value.Args[0].Args[1]; // todo: generalize
                                    flow = flow.Substitute(f.RectRateA, delta); // replace A from \dot{x} \in [A,B] with \delta which exists in [A,B]

                                    flow = z3.MkEq(f.Value.Args[0].Args[0], flow);
                                    BoolExpr[] andTerms = { (BoolExpr)flow, z3.MkGe((ArithExpr)delta, (ArithExpr)f.RectRateA), z3.MkLe((ArithExpr)delta, (ArithExpr)f.RectRateB) }; // constrain: A <= delta <= B
                                    flow = z3.MkAnd(andTerms);
                                    exprlist.Add((BoolExpr)flow);
                                    break;
                                }
                            case Flow.DynamicsTypes.timed:
                            default:
                                {
                                    exprlist.Add((BoolExpr)f.Value);
                                    break;
                                }
                        }
                    }
                }

                List<Expr> bt = new List<Expr>();
                //hidx = z3.MkConst("h", Controller.Instance.IndexType);
                Expr hidx = z3.MkIntConst("h");
                bt.Add(hidx);

                if (Controller.Instance.TimeOption == Controller.TimeOptionType.separated)
                {
                    exprlist.Add((BoolExpr)l.StatePredicate); // control location, e.g., q[h] == 2
                }

                expr = z3.MkAnd(exprlist.ToArray());

                if (Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction)
                {
                    expr = z3.MkImplies((BoolExpr)l.StatePredicate, (BoolExpr)expr); // control location, e.g., q[h] == 2 implies (inv, guard, flow, etc.)
                }

                expr = expr.Substitute(Controller.Instance.Indices["i"], hidx); // replace i by h

                // if we haven't yet add every location's invariant, keep adding them on
                if (Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction && timeall.Count < h.Locations.Count)
                {
                    timeall.Add((BoolExpr)expr);

                    if (timeall.Count != h.Locations.Count)
                    {
                        continue;
                    }
                }



                //expr = z3.MkAnd( discreteall.ToArray() );
                //expr = z3.MkExists(Controller.Instance.ExistentialConstants.Values.ToArray(), expr); // todo: only do this for termination properties
                //Console.WriteLine("GENERATED INVARIANT MODEL (explicit quantifiers)\n\r");
                //z3.checkTerm(expr, out model, out core, true);


                expr = z3.MkAnd(timeall.ToArray());

                Expr tid = z3.timeIdentity(hidx);

                // for bounded-model checking: do the state rename outside the quantifiers
                if (k > 0)
                {
                    z3.unprimeAllVariables(ref expr, k);
                    z3.unprimeAllVariables(ref tid, k);
                }

                // quantifier order (code in reverse order next as we build them up one after another)
                // exists t_1 . forall i . exists delta . forall t_2
                // t_1: the amount of time to elapse
                // i: process identifier
                // delta: delta is any value lying between the minimum and maximum rectangular constraints
                // t_2: time used to enforce stopping condition and invariant along the entire trajectory

                // if we have a stop condition, or if we're doing the conjunction (assume at least one location has a stop)
                if (l.Stop != null || Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction)
                {
                    expr = z3.MkForall(new Expr[] { t2 }, z3.MkImplies(z3.MkAnd(z3.MkGe(t2, Controller.Instance.RealZero), z3.MkLe(t2, t1)), (BoolExpr)expr)); // NO, MUST BE IMPLIES!!! todo: seems correct with this as and instead of implies, doulbe check
                }

                expr = z3.MkExists(new Expr[] { delta }, expr);
                BoolExpr idxConstraint = z3.MkAnd(z3.MkGe((ArithExpr)hidx, (ArithExpr)Controller.Instance.IndexOne), z3.MkLe((ArithExpr)hidx, (ArithExpr)Controller.Instance.IndexN));

                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.naturalOneToN:
                        {
                            switch (Controller.Instance.ExistsOption)
                            {
                                case Controller.ExistsOptionType.and:
                                    expr = z3.MkForall(bt.ToArray(), z3.MkImplies(idxConstraint, z3.MkAnd((BoolExpr)expr, (BoolExpr)tid)));
                                    break;
                                case Controller.ExistsOptionType.implies:
                                default:
                                    expr = z3.MkForall(bt.ToArray(), z3.MkImplies(idxConstraint, z3.MkAnd((BoolExpr)expr, (BoolExpr)tid)));
                                    break;
                            }
                            break;
                        }
                    case Controller.IndexOptionType.integer:
                    case Controller.IndexOptionType.enumeration:
                    default:
                        expr = z3.MkForall(bt.ToArray(), z3.MkAnd((BoolExpr)expr, (BoolExpr)tid));
                        break;
                }

                switch (Controller.Instance.ExistsOption)
                {
                    case Controller.ExistsOptionType.and:
                        expr = z3.MkExists(new Expr[] { t1 }, z3.MkAnd(z3.MkGe(t1, Controller.Instance.RealZero), (BoolExpr)expr)); // broken with invariants if using implies
                        break;
                    case Controller.ExistsOptionType.implies:
                    default:
                        expr = z3.MkExists(new Expr[] { t1 }, z3.MkImplies(z3.MkGt(t1, Controller.Instance.RealZero), (BoolExpr)expr));
                        break;
                }


                timeii = z3.MkAnd((BoolExpr)timeii, (BoolExpr)expr);
            }
            return timeii;
        }

        /**
         * Print the system in HyXML form by walking the data structure
         */
        public void PrintHyXML()
        {
            // need helper to print a Z3 term in infix form
            
        }

        /**
         * Determine if a set of properties can be reached by the system
         */
        public void checkBackReachable()
        {
        }

        /**
         * Determine if a given property specified by p can be reached by the system
         */
        public Boolean checkBackReachableNonempty(Expr p)
        {
            return true;
        }


        /**
         * Make terms corresponding to pre and post-state for a transition (can be local or global transition)
         */
        public Expr makeTransitionTerm(Transition t, ConcreteLocation l, Expr idx, params uint[] paramList)
        {
            uint N = 0;
            uint quant = 0;
            uint k = 0;
            if (paramList != null && paramList.Length > 0)
            {
                N = paramList[0];
                if (paramList.Length > 1)
                {
                    k = paramList[1];
                }
                if (paramList.Length > 2)
                {
                    quant = paramList[2];
                }
            }

            List<BoolExpr> locInvariant = new List<BoolExpr>();

            if (l != null)
            {
                locInvariant.Add((BoolExpr)l.StatePredicate); // discrete location prestate   (e.g., loc[i]  = 1)
            }
            if (t.NextStates.Count > 0)
            {
                locInvariant.Add((BoolExpr)t.ToTerm());       // discrete location post-state (e.g., loc'[i] = 2)
            }

            // add guard, if one exists
            if (t.Guard != null)
            {
                locInvariant.Add((BoolExpr)t.Guard);
            }

            if (l != null)
            {
                // add invariant, if one exists
                if (l.Invariant != null)
                {
                    locInvariant.Add((BoolExpr)l.Invariant);
                }

                // add stopping condition, if one exists
                if (l.Stop != null)
                {
                    locInvariant.Add((BoolExpr)l.Stop);
                }
            }

            List<String> globalVariableResets = new List<String>(); // global variables not reset
            List<String> indexVariableResets = new List<String>();  // indexed variables of process moving that are not reset
            List<String> universalIndexVariableResets = new List<String>();  // universally quantified indexed variables that are reset

            if (t.Reset != null)
            {
                locInvariant.Add((BoolExpr)t.Reset);

                globalVariableResets = z3.findGlobalVariableResets(t.Reset);
                indexVariableResets = z3.findIndexedVariableResets(t.Reset);
            }
            else
            {
                // global variable was not mentioned since reset is null: add it to the identity global variables (g' = g)
                globalVariableResets = z3.findGlobalVariableResets(null);
                indexVariableResets = z3.findIndexedVariableResets(null);
            }

            if (t.UGuard != null)
            {
                universalIndexVariableResets = z3.findIndexedVariableResetsNeg(t.UGuard);
            }

            Expr locInvariantAnd = null;
            // create conjunction of pre-state and post-state conditions
            if (locInvariant.Count > 0)
            {
                locInvariantAnd = z3.MkAnd(locInvariant.ToArray());
            }

            Expr identity;
            if (l == null)
            {
                // TODO NEXT: GLOBAL INDEXED VARIABLE COULD CAUSE RESETS / "be the process moving"
                int i = 0;
                Expr gidx = null;
                foreach (var v in Controller.Instance.GlobalVariables)
                {
                    if (Controller.Instance.Sys.Variables.Find(
                        delegate(Variable gv) {
                            return gv.Name == v.Key;
                        }).Type == Variable.VarType.index && z3.findTerm(t.Reset, v.Value, true))
                    {
                        gidx = v.Value;
                        i++;
                    }
                    // TODO: need to refactor forall identity to allow multiple processes moving, for now throw exception if it happens
                    if (i > 1)
                    {
                        throw new Exception("Error: too many global index variables used.");
                    }

                }
                identity = z3.forallIdentity(gidx, globalVariableResets, indexVariableResets, universalIndexVariableResets, t.UGuard, N); // no process moves if no location
            }
            else
            {
                identity = z3.forallIdentity(idx, globalVariableResets, indexVariableResets, universalIndexVariableResets, t.UGuard, N);
            }

            if (locInvariantAnd == null && N == 0)
            {
                locInvariantAnd = identity;
            }
            else if (N == 0)
            {
                locInvariantAnd = z3.MkAnd((BoolExpr)locInvariantAnd, (BoolExpr)identity);
            }

            if (l != null && N == 0)
            {
                locInvariantAnd = locInvariantAnd.Substitute(Controller.Instance.Indices["i"], idx); // replace i by h

                BoolExpr idxConstraint = z3.MkAnd(z3.MkGe((ArithExpr)idx, (ArithExpr)Controller.Instance.IntOne), z3.MkLe((ArithExpr)idx, (ArithExpr)Controller.Instance.IndexN));

                // add quantifiers based on pre-state and post-state, using implies vs. and options and indexing options
                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.naturalOneToN:
                        switch (Controller.Instance.ExistsOption)
                        {
                            case Controller.ExistsOptionType.and:
                                locInvariantAnd = z3.MkAnd(idxConstraint, (BoolExpr)locInvariantAnd); // 1 <= h <= N, enforce identity for all other processes not moving
                                break;
                            case Controller.ExistsOptionType.implies:
                            default:
                                locInvariantAnd = z3.MkImplies(idxConstraint, (BoolExpr)locInvariantAnd); // 1 <= h <= N, enforce identity for all other processes not moving
                                break;
                        }
                        break;
                    case Controller.IndexOptionType.enumeration:
                    case Controller.IndexOptionType.integer:
                    default:
                        //locInvariantAnd = locInvariantAnd & z3.forallIdentity(hidx, globalVariableResets, indexVariableResets);
                        break;
                }
            }

            if (N == 0)
            {
                // todo: add quantifier: check if correct
            }
            else
            {
                List<BoolExpr> transAll = new List<BoolExpr>();
                // expand quantifier manually
                for (uint i = 1; i <= N; i++)
                {
                    Expr numidx = z3.MkInt(i);
                    //Expr trans = locInvariantAnd.Substitute(idx, numidx); // instantiate i
                    //transAll.Add(z3.MkAnd(z3.MkEq(idx, numidx), (BoolExpr)locInvariantAnd)); // simply set symbol idx = value idx
                    BoolExpr copy = (BoolExpr)z3.copyExpr(locInvariantAnd);

                    foreach (var v in this.HybridAutomata[0].Variables)
                    {
                        //copy.Substitute(z3.MkApp(v.Value, idx), z3.MkApp(v.Value, numidx)); // substitute to function
                        idx = z3.MkIntConst("i");
                        copy = (BoolExpr)copy.Substitute(z3.MkApp(v.Value, idx), this.ReachValues[new Tuple<string,uint,uint>(v.Name, k, i)]); // substitute to constant (needed for doing q.e.)
                        copy = (BoolExpr)copy.Substitute(z3.MkApp(v.ValuePrimed, idx), this.ReachValues[new Tuple<string,uint,uint>(v.Name, k+1, i)]); // substitute to constant (needed for doing q.e.)
                        copy = (BoolExpr)copy.Substitute(idx, numidx);
                    }

                    copy = z3.MkAnd(copy, (BoolExpr)z3.forallIdentity(z3.MkInt(i), globalVariableResets, indexVariableResets, universalIndexVariableResets, t.UGuard, N));

                    for (uint j = 1; j <= N; j++)
                    {
                        if (j == i)
                        {
                            continue;
                        }
                        foreach (var v in this.HybridAutomata[0].Variables)
                        {
                            copy = (BoolExpr)copy.Substitute(z3.MkApp(v.Value, z3.MkInt(j)), this.ReachValues[new Tuple<string, uint, uint>(v.Name, k, j)]); // substitute to constant (needed for doing q.e.)
                            copy = (BoolExpr)copy.Substitute(z3.MkApp(v.ValuePrimed, z3.MkInt(j)), this.ReachValues[new Tuple<string, uint, uint>(v.Name, k + 1, j)]); // substitute to constant (needed for doing q.e.)
                        }
                    }
                    transAll.Add(copy);
                }
                locInvariantAnd = z3.MkOr(transAll.ToArray());
            }
            return locInvariantAnd;
        }

        /**
         * tmpterm is modified to create the appropriate term for a flow transition
         * v is the variable
         * varTerm is the term corresponding to the variable (e.g., Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")])
         */
        public Expr makeFlowTransitionTerm(Expr tmpterm, Variable v, Expr varTerm, Location l, Expr t1, Expr t2, Expr delta)
            // TODO: remove varTerm, and add an object to variable that references back to the global dictionary of variables...? might be a little tricky for global vs indexed
        {
            if (v.UpdateType == Variable.VarUpdateType.continuous)
            {
                switch (Controller.Instance.DataOption)
                {
                    case Controller.DataOptionType.array:
                        {
                            tmpterm = tmpterm.Substitute(Controller.Instance.DataA.IndexedVariableDecl[v.Name], Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name]);
                            break;
                        }
                    case Controller.DataOptionType.uninterpreted_function:
                    default:
                        {
                            //z3.replaceFuncDecl(ref tmpterm, tmpterm, Controller.Instance.DataU.IndexedVariableDecl[v.Name], Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], false);

                            if (l.Flows != null && l.Flows.Count > 0)
                            {
                                foreach (Flow f in l.Flows)
                                {
                                    switch (f.DynamicsType)
                                    {
                                        case Flow.DynamicsTypes.constant:
                                            {
                                                continue;
                                            }
                                        case Flow.DynamicsTypes.timed:
                                            {
                                                Expr flowInv = f.Value;
                                                flowInv = flowInv.Args[1];
                                                flowInv = flowInv.Substitute(t1, t2); // replace t1 with t2
                                                tmpterm = tmpterm.Substitute(varTerm, flowInv); // replace in full term
                                                break;
                                            }
                                        case Flow.DynamicsTypes.rectangular:
                                        default:
                                            {
                                                /*
                                                Term flowInvA = f.Value;
                                                Term flowInvB = f.Value;
                                                flowInvA = flowInvA.GetAppArgs()[0].GetAppArgs()[1];
                                                flowInvB = flowInvB.GetAppArgs()[1].GetAppArgs()[1];
                                                z3.replaceTerm(ref flowInvA, flowInvA, t1, t2, true); // replace t1 with t2
                                                z3.replaceTerm(ref flowInvB, flowInvB, t1, t2, true); // replace t1 with t2

                                                Term tmptermA = tmpterm;
                                                Term tmptermB = tmpterm;

                                                z3.replaceTerm(ref tmptermA, tmptermA, varTerm, flowInvA, false);
                                                z3.replaceTerm(ref tmptermB, tmptermB, varTerm, flowInvB, false);

                                                //tmpterm = tmptermA & tmptermB;
                                                tmpterm = tmptermB;
                                                 * */

                                                Expr flowInv = f.Value;
                                                flowInv = f.Value.Args[0].Args[1];
                                                flowInv = flowInv.Substitute(t1, t2); // replace t1 with t2
                                                flowInv = flowInv.Substitute(f.RectRateA, delta); // replace A from \dot{x} \in [A,B] with \delta which exists in [A,B]
                                                tmpterm = tmpterm.Substitute(varTerm, flowInv);

                                                break;
                                            }
                                    }
                                }
                            }
                            break;
                        }
                }
            }

            return tmpterm;
        }


        public void boundedModelCheckAllProperties()
        {
            foreach (Property p in this.Properties)
            {
                Boolean result = boundedModelCheck(Controller.Instance.IndexNValue, 100, p.Formula); // use our own BMC
                //Boolean result = fixedpointCheck(2, 100, p.Formula); // use the Z3 provided fixed-point framework

                if (result)
                {
                    Console.WriteLine("Property satisfied: " + p.ToString());
                }
                else
                {
                    Console.WriteLine("Property unsatisfied in k rounds: " + p.ToString());
                }
            }
        }

        public Boolean fixedpointCheck(int N, int k, Expr predicate)
        {
            AHybridAutomaton h = this._has.First();



            Microsoft.Z3.Fixedpoint fp = z3.MkFixedpoint();

            /*
            (set-option :dl-compile-with-widening true)
(set-option :dl-unbound-compressor false)

(declare-fun l0 (Int Int) Bool)
(declare-fun l1 (Int Int) Bool)
(set-predicate-representation l0 interval_relation bound_relation)
(set-predicate-representation l1 interval_relation bound_relation)

(rule (forall ((m Int)) (l0 0 m)))
(rule (forall ((x0 Int) (x Int) (m Int))
              (=> (and (l0 x0 m) (= x (+ x0 1)) (<= x0 m)) (l0 x m))))
(rule (forall ((x Int) (m Int))
              (=> (and (l0 x m) (< m x)) (l1 x m))))
(query (exists ((y Int) (m Int)) (l1 y m)))
             * */

            FuncDecl l0 = z3.MkFuncDecl("l0", new Sort[] { z3.MkIntSort(), z3.MkIntSort() }, z3.MkBoolSort());
            FuncDecl l1 = z3.MkFuncDecl("l1", new Sort[] { z3.MkIntSort(), z3.MkIntSort() }, z3.MkBoolSort());

            fp.RegisterRelation(l0);
            fp.RegisterRelation(l1);

            //todo next, how?
            fp.SetPredicateRepresentation(l0, new Symbol[] { z3.MkSymbol("interval_relation"), z3.MkSymbol("bound_relation")});
            fp.SetPredicateRepresentation(l1, new Symbol[] { z3.MkSymbol("interval_relation"), z3.MkSymbol("bound_relation") });

            Expr m = z3.MkIntConst("m");
            Expr x = z3.MkIntConst("x");
            Expr x0 = z3.MkIntConst("x0");
            Expr y = z3.MkIntConst("y");
            fp.AddRule(z3.MkForall(new Expr[] { m }, z3.MkApp(l0, z3.MkInt(0), m)));
            fp.AddRule(z3.MkForall(new Expr[] { x0, x, m }, z3.MkImplies(z3.MkAnd((BoolExpr)z3.MkApp(l0, x0, m), z3.MkEq(x, z3.MkAdd((ArithExpr)x0, z3.MkInt(1))), z3.MkLe((ArithExpr)x0, (ArithExpr)m)), (BoolExpr)z3.MkApp(l0, x, m))));
            fp.AddRule(z3.MkForall(new Expr[] { x, m }, z3.MkImplies(z3.MkAnd((BoolExpr)z3.MkApp(l0, x, m), z3.MkLt((ArithExpr)m, (ArithExpr)x)), (BoolExpr)z3.MkApp(l1, x, m))));

            Status fps = fp.Query(z3.MkExists(new Expr[] { y, m }, z3.MkApp(l1, y, m)));
            Expr fpa = fp.GetAnswer();

            Console.WriteLine(fps.ToString());
            Console.WriteLine(fpa.ToString());

            /*List<Expr> cts = makeTransitions(N, k, h.Initial);
            foreach (Expr c in cts)
            {
                fp.AddRule((BoolExpr)c);
            }

            fp.Query((BoolExpr)predicate);*/
            return false;
        }

        public class ReachStructure
        {
            public Expr ReachedStates = Controller.Instance.Z3.MkFalse();
            public List<Expr> TransitionSequence = new List<Expr>();
            public uint Step;

            public ReachStructure(uint k, params BoolExpr[] seq)
            {
                this.Step = k;
                this.Add(seq);
            }

            public void Add(params BoolExpr[] seq)
            {
                this.TransitionSequence.AddRange(seq);


                // invariant ensures all states are either labeled with 0, or the most recent transition number
                //for (uint kfrom = 1; kfrom <= this.Step; k++)
                //{
                //}

                if (seq.Length == 0)
                {
                }
                else if (seq.Length == 1)
                {
                    this.ReachedStates = Controller.Instance.Z3.MkOr((BoolExpr)this.ReachedStates, seq[0]);
                }
                else
                {
                    this.ReachedStates = Controller.Instance.Z3.MkOr((BoolExpr)this.ReachedStates, Controller.Instance.Z3.MkOr(seq));
                }
                Controller.Instance.Z3.unprimeAllVariablesReachability(ref this.ReachedStates, 0, this.Step); // rename all states to 0

                ////Tactic tqe = Controller.Instance.Repeat(z3.Then(z3.MkTactic("simplify"), z3.MkTactic("ctx-simplify"), z3.Repeat(z3.Then(z3.MkTactic("elim-and"), z3.OrElse(z3.MkTactic("split-clause"), z3.MkTactic("skip")))), z3.MkTactic("simplify"), z3.MkTactic("propagate-values"), z3.MkTactic("propagate-ineqs")));
                //Tactic tqe = Controller.Instance.Z3.MkTactic("qe");
                //Goal g = Controller.Instance.Z3.MkGoal(true);
                ////g.Assert(Controller.Instance.Z3.Assumptions.ToArray()); // basic assumptions

                //foreach (var v in Controller.Instance.IndexedVariables)
                //{

                //}

                //g.Assert((BoolExpr)ReachedStates);
                //Params p = z3.MkParams();
                //p.Add("PI_AVOID_SKOLEMS", true);
                //p.Add("PI_PULL_QUANTIFIERS", true);
                //p.Add("PI_USE_DATABASE", true);
                //ApplyResult ar = tqe.Apply(g, p);

                //ar = ar;

                //System.Console.WriteLine("After simplify:" + ar.ToString());

                //List<BoolExpr> sgfall = new List<BoolExpr>();
                //foreach (var sgf in ar.Subgoals)
                //{
                //    sgfall.AddRange(sgf.Formulas);
                //}
            }
        }


        /**
         * Perform bounded model checking using a fixed value of N for up to k rounds, checking if the property predicate is ever violated
         */
        public Boolean boundedModelCheck(uint N, uint K, Expr predicate)
        {
            Boolean satisfied = false;
            Boolean terminate = false;
            Model model;
            Expr[] core;

            AHybridAutomaton h = this._has.First();

            //pmode enum { mode_fifo, mode_lifo };

            //Stack<Expr> previousStates = new Stack<Expr>();
            //Queue<Expr> previousStates = new Queue<Expr>();
            SortedDictionary<uint, ReachStructure> previousStates = new SortedDictionary<uint, ReachStructure>();
            Expr predicatek = z3.MkFalse();
            //Expr init = h.Initial;
            Expr init;
            List<BoolExpr> initList = new List<BoolExpr>();

            foreach (var v in this.HybridAutomata[0].Variables)
            {
                for (uint i = 1; i <= N; i++)
                {
                    this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name, 0, i), z3.MkConst(v.Name + 0 + "_" + i, v.TypeSort));
                    this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name,  1, i), z3.MkConst(v.Name + ( 1) + "_" + i, v.TypeSort));
                }
            }

            // make initial condition expression
            for (uint i = 1; i <= N; i++)
            {
                
                BoolExpr qinit = z3.MkFalse();
                foreach (var l in h.Locations)
                {
                    if (l.Initial)
                    {
                        qinit = z3.MkOr(qinit, (BoolExpr)l.StatePredicate.Substitute(Controller.Instance.Indices["i"], z3.MkInt(i)));
                    }
                }
                Expr tmpi = (BoolExpr)h.Initial;

                if (Controller.Instance.IndexedVariables.Count > 0)
                {
                    
                    Expr iConst = Controller.Instance.Z3.MkNumeral(i, Controller.Instance.IndexType);
                    tmpi = tmpi.Substitute(Controller.Instance.Indices["i"], iConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)

                    // todo: huge hack
                    while (tmpi.ASTKind != Z3_ast_kind.Z3_QUANTIFIER_AST && tmpi.NumArgs > 0)
                    {
                        tmpi = tmpi.Args[0];
                    }
                    if (tmpi.ASTKind == Z3_ast_kind.Z3_QUANTIFIER_AST)
                    {
                        Quantifier qi = ((Quantifier)tmpi);
                        
                        tmpi = ((Quantifier)tmpi).Body;
                        /*
                        int c = 0;
                        foreach (var v in qi.BoundVariableNames)
                        {
                            Expr s = z3.MkApp(z3.MkFuncDecl(z3.MkSymbol(":var"), z3.IntSort, qi.BoundVariableSorts[c]), z3.MkInt(c));
                            tmpi = tmpi.Substitute(s, z3.MkInt(i));
                            c++;
                        }*/
                    }
                    if (tmpi.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_IMPLIES || tmpi.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_OR) // may have simplified implies to not or form
                    {
                        tmpi = tmpi.Args[1];
                    }

                    // horrible hack, can't create the necessary (:var 0) expression to replace in api, so convert to string, string replace, re-parse
                    String tmp = Controller.Instance.Z3.ToStringFormatted(tmpi, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                    //tmp = tmp.Replace("[i]", "_" + i.ToString());
                    tmp = tmp.Replace("#0",  i.ToString()); // z3 3.2 format
                    tmp = tmp.Replace("(:var 0)",  i.ToString()); // z3 4.0 format
                    tmp = tmp.Replace("&", "and");

                    
                    Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(tmp);
                    tmpi = passel.controller.parsing.math.ast.LogicalExpression.CreateTerm(tmptree);

                    tmpi = z3.MkAnd(qinit, (BoolExpr)tmpi);


                    foreach (var v in this.HybridAutomata[0].Variables)
                    {
                        tmpi = (BoolExpr)tmpi.Substitute(z3.MkApp(v.Value, iConst), this.ReachValues[new Tuple<string, uint, uint>(v.Name, 0, i)]); // substitute to constant (needed for doing q.e.)
                        tmpi = (BoolExpr)tmpi.Substitute(z3.MkApp(v.ValuePrimed, iConst), this.ReachValues[new Tuple<string, uint, uint>(v.Name, 1, i)]); // substitute to constant (needed for doing q.e.)
                    }
                    

                    initList.Add((BoolExpr)tmpi);

                    
                }
            }
            init = z3.MkAnd(initList.ToArray());

            //z3.Assumptions.RemoveAll(a => a.IsQuantifier);
            this.z3.slvr.Assert(this.z3.Assumptions.ToArray()); // assert all the data-type assumptions
            this.z3.slvr.Assert(this.z3.AssumptionsUniversal.ToArray()); // assert all the data-type assumptions
            //init = z3.MkAnd((BoolExpr)init, (BoolExpr)z3.MkAnd(z3.Assumptions.ToArray()));

            z3.unprimeAllVariables(ref init, 1); // rename with 0 indexing (no primed variables, so only unprimed -> 0)

            previousStates.Add(0, new ReachStructure( 0, (BoolExpr)init ));
            //previousStates.Enqueue(init);
            //previousStates.Push(init);


            // loop over bound
            for (uint k = 1; k <= K && !terminate; k++)
            {
                previousStates.Add(k, new ReachStructure(k));

                // termination condition --- no further transitions enabled
                if (previousStates[k-1].TransitionSequence.Count == 0 || terminate)
                {
                    List<Expr> asdfL = new List<Expr>();

                    String asdf = "asdfasdfasdfadsf"; // temp crap to get debugger to break here
                    bool nop = false;
                    nop = true;
                    nop = false;
                    asdf = "";

                    break;
                }

                foreach (Expr last in previousStates[k-1].TransitionSequence)
                {


                    Expr predicatektmp = this.z3.MkNot((BoolExpr)predicate); // todo: predicates are mostly safety properties, not bad / unsafety properties, so we negate them
                    z3.unprimeAllVariables(ref predicatektmp, k); // rename with k indexing
                    predicatek = z3.MkOr((BoolExpr)predicatek, (BoolExpr)predicatektmp);


                    if (k == 1)
                    {
                        Expr claim = z3.MkAnd((BoolExpr)init, (BoolExpr)predicatek);

                        //Expr tmp = z3.Simplify(init);
                        //tmp = z3.Simplify(predicatek);

                        //claim = z3.Simplify(claim);

                        // intersected with predicate
                        if (z3.checkTerm(claim, out model, out core, true))
                        {
                            //satisfied = true;
                            //terminate = true;
                            //break;
                        }
                    }


                    //Expr last = previousStates.Dequeue();
                    //Expr last = previousStates.Pop(); // for LIFO version with stack
                    //todo: log all these so we can compare the sequence easily

                    // add new state variables for round k
                    foreach (var v in this.HybridAutomata[0].Variables)
                    {
                        for (uint i = 1; i <= N; i++)
                        {
                            //this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name, k, i), z3.MkConst(v.Name + k + "_" + i, v.TypeSort));
                            this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name, k+1, i), z3.MkConst(v.Name + (k+1) + "_" + i, v.TypeSort));
                        }
                    }


                    List<Expr> cts = new List<Expr>();
                    //cts.Add(makeTimeTransition(N, k, last));
                    cts.AddRange(makeTransitions(N, k-1, last, 0));


                    for (int ti = 0; ti < cts.Count; ti++)
                    {
                        Expr t = cts[ti];

                        if (z3.checkTerm(t, out model, out core, true)) // only add if it's satisfiable, otherwise it's a disabled transition
                        {
                            if (model != null)
                            {
                                System.Console.WriteLine("Model for transition to be taken: \n\r\n\r");
                                System.Console.WriteLine(model.ToString());
                            }

                            /*
                            Tactic tqe = z3.Repeat(z3.Then(z3.MkTactic("simplify"), z3.MkTactic("ctx-simplify"), z3.Repeat(z3.Then(z3.MkTactic("elim-and"), z3.OrElse(z3.MkTactic("split-clause"), z3.MkTactic("skip")))), z3.MkTactic("simplify"), z3.MkTactic("propagate-values"), z3.MkTactic("propagate-ineqs")));
                            Goal g = z3.MkGoal(true);
                            g.Assert(z3.Assumptions.ToArray()); // basic assumptions
                            g.Assert((BoolExpr)t);
                            Params p = z3.MkParams();
                            p.Add("PI_AVOID_SKOLEMS", true);
                            p.Add("PI_PULL_QUANTIFIERS", true);
                            p.Add("PI_USE_DATABASE", true);
                            ApplyResult ar = tqe.Apply(g, p);

                            ar = ar;

                            System.Console.WriteLine("After simplify:" + ar.ToString());

                            List<BoolExpr> sgfall = new List<BoolExpr>();
                            foreach (var sgf in ar.Subgoals)
                            {
                                sgfall.AddRange(sgf.Formulas);
                            }
                            previousStates[k].Add( z3.MkAnd(sgfall.ToArray()) ); */

                            previousStates[k].Add( (BoolExpr)t );

                            

                            //previousStates.Enqueue(t);
                            //previousStates.Push(t);

                            //Expr claim = z3.MkAnd((BoolExpr)t, (BoolExpr)predicatek);

                            // intersected with predicate
                            /*
                            if (z3.checkTerm(claim, out model, out core, true))
                            {
                                satisfied = true;
                                terminate = true;
                                break;
                            }
                             */

                            // fixed point check
                            // term last needs to have its variables replaced (increment state indexes by 1?)
                            //Term fp = z3.MkImplies(t, last);
                            /*Term fp = t & !last; // P and \neg B, where P is current, B is previous
                            Console.WriteLine("fixed point check:");
                            Console.WriteLine(fp.ToString());
                            String s;
                            if (!z3.checkTerm(fp, out model, out core, true))
                                // use true for proveterm with implies version
                            {
                                previousStates.Pop(); // pop last term inserted: was fixed-point
                                break;
                            }*/
                        }
                        else
                        {
                            Console.WriteLine("disabled transition: ");
                            Console.WriteLine(t.ToString());
                        }

                    }
                }
            }

            return satisfied;
        }

        public List<Expr> makeTransitions(uint N, uint k, Expr current, uint quant)
        {
            List<Expr> transitionTerms = new List<Expr>();
            AHybridAutomaton h = this._has.First();

            foreach (ConcreteLocation l in h.Locations)
            {
                foreach (var t in l.Transitions)
                {
                    Expr currentWithTransition = current;

                    if (quant > 0)
                    {
                        List<Expr> bound = new List<Expr>();
                        //Expr hidx = z3.MkConst("h" + k.ToString(), Controller.Instance.IndexType);
                        Expr hidx = z3.MkIntConst("h" + k.ToString());
                        bound.Add(hidx);

                        Expr trans = (BoolExpr)this.makeTransitionTerm(t, l, hidx);
                        z3.unprimeAllVariables(ref trans, k); // renamed with k

                        currentWithTransition = z3.MkAnd((BoolExpr)currentWithTransition, (BoolExpr)trans);
                        currentWithTransition = z3.MkExists(bound.ToArray(), currentWithTransition);
                        transitionTerms.Add(currentWithTransition);
                    }
                    else
                    {
                        Expr hidx = z3.MkIntConst("h" + k.ToString());
                        BoolExpr tt = (BoolExpr)this.makeTransitionTerm(t, l, hidx, N, k, quant);
                        foreach (var v in tt.Args)
                        {
                            currentWithTransition = current;
                            currentWithTransition = z3.MkAnd((BoolExpr)currentWithTransition, (BoolExpr)v);
                            z3.unprimeAllVariables(ref currentWithTransition, k); // renamed with k
                            transitionTerms.Add(currentWithTransition);
                        }
                    }
                }
            }
            return transitionTerms;
        }

        public Expr makeTimeTransition(uint N, uint k, Expr current)
        {
            AHybridAutomaton h = this._has.First();
            return this.makeFlowsAll(h, current, k);
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
    }
}


// todo tomorrow:
// 1) add stopping condition support, currently just eliminates the null quantifier
// 2) once adding this, debug the first property: <property equn='forall i ((q[i] == cs) implies x[i] &gt;= B)' type='safety' /> when we remove the reset on x[i]', so it is inductive over a single transition
// 3) add assumptions on g at header as was done for indexed variables: it should lie between 0 and N if it's of ID_{\bot} type


// todo today:
// 1) add global variables and index variables post-states are equal to their prestates on the timed transitions
// 2) create giant disjunct of all timed transitions instead of doing it one by one as is now?

// todo long-term
// 1) multi-thread? check a property in each thread?

// todo 12/4
// 3) pretty printer for latex output

// todo 12/7
// 0) finish fixing / debugging nfa example before moving on to more complex ones
// 1) http://stackoverflow.com/questions/8374145/expressing-a-subtype-relation-between-enumeration-types-in-z3
//    use subtype relation on enumeration datatypes to declare bottom index

// todo 12/7
// 0) need to make disjunction across all states for timed transition it seems.
//    e.g., if q[i] = 1, then flow, stop, inv are defined according to location 1, while if q[i] = 2, they must be defined according to state 2. checking across each may not be equivalent
// 1) make the location sort a finite enumeration sort? or a bitvector of fixed size?

// todo 12/8
// 0) make lists of inductive invariants vs inductive properties


// todo 1/30
// 0) check weird property bug for fischer: check using model by plugging in to see how it's sat; check using identity transition