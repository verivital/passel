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
                                p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claim));
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
                                    p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claim));
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

                        Expr timeii = p.Formula;

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
                        hidx = z3.MkIntConst("h");
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

                        // quantifier order (code in reverse order next as we build them up one after another)
                        // exists t_1 . forall i . exists delta . forall t_2
                        // t_1: the amount of time to elapse
                        // i: process identifier
                        // delta: delta is any value lying between the minimum and maximum rectangular constraints
                        // t_2: time used to enforce stopping condition and invariant along the entire trajectory

                        // if we have a stop condition, or if we're doing the conjunction (assume at least one location has a stop)
                        if (l.Stop != null || Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction)
                        {
                            expr = z3.MkForall(new Expr[] { t2 }, z3.MkImplies( z3.MkAnd(z3.MkGe( t2, Controller.Instance.RealZero), z3.MkLe(t2, t1)), (BoolExpr)expr)); // NO, MUST BE IMPLIES!!! todo: seems correct with this as and instead of implies, doulbe check
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
                                            expr = z3.MkForall(bt.ToArray(), z3.MkImplies(idxConstraint, z3.MkAnd((BoolExpr)expr, (BoolExpr)z3.timeIdentity(hidx))));
                                            break;
                                        case Controller.ExistsOptionType.implies:
                                        default:
                                            expr = z3.MkForall(bt.ToArray(), z3.MkImplies(idxConstraint, z3.MkAnd((BoolExpr)expr, (BoolExpr)z3.timeIdentity(hidx))));
                                            break;
                                    }
                                    break;
                                }
                            case Controller.IndexOptionType.integer:
                            case Controller.IndexOptionType.enumeration:
                            default:
                                expr = z3.MkForall(bt.ToArray(), z3.MkAnd((BoolExpr)expr, (BoolExpr)z3.timeIdentity(hidx)));
                                break;
                        }

                        switch (Controller.Instance.ExistsOption)
                        {
                            case Controller.ExistsOptionType.and:
                                expr = z3.MkExists(new Expr[] { t1 }, z3.MkAnd( z3.MkGe(t1, Controller.Instance.RealZero), (BoolExpr)expr)); // broken with invariants if using implies
                                break;
                            case Controller.ExistsOptionType.implies:
                            default:
                                expr = z3.MkExists(new Expr[] { t1 }, z3.MkImplies( z3.MkGt(t1, Controller.Instance.RealZero), (BoolExpr)expr));
                                break;
                        }


                        timeii = z3.MkAnd((BoolExpr)timeii, (BoolExpr)expr);
                        p.addInductiveInvariant(timeii);

                        //if (z3.checkTerm(timeii, out model, out core, true))
                        //if (z3.proveTerm(inductiveInvariant, out model, out core, true))
                        if (true)
                        {
                            z3.checkTerm(timeii, out model, out core, true);


                            timeii = z3.MkImplies((BoolExpr)timeii, (BoolExpr)p.Post);

                            timeii = z3.MkExists(Controller.Instance.ExistentialConstants.Values.ToArray(), timeii); // todo: only do this for termination properties

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
                                p.Counterexamples.Add(new Counterexample(z3.slvr.Model, timeii));
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
        public Expr makeTransitionTerm(Transition t, ConcreteLocation l, Expr idx)
        {
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
                identity = z3.forallIdentity(gidx, globalVariableResets, indexVariableResets, universalIndexVariableResets, t.UGuard); // no process moves if no location
            }
            else
            {
                identity = z3.forallIdentity(idx, globalVariableResets, indexVariableResets, universalIndexVariableResets, t.UGuard);
            }
            //identity = z3.MkTrue(); // TODO: delete, debugging

            if (locInvariantAnd == null)
            {
                locInvariantAnd = identity;
            }
            else
            {
                locInvariantAnd = z3.MkAnd((BoolExpr)locInvariantAnd, (BoolExpr)identity);
            }

            if (l != null)
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

        enum outmode { MODE_PHAVER, MODE_HYTECH };




        public void boundedModelCheckAllProperties()
        {
            foreach (Property p in this.Properties)
            {
                //Boolean result = boundedModelCheck(2, 100, p.Formula); // use our own BMC
                Boolean result = fixedpointCheck(2, 100, p.Formula); // use the Z3 provided fixed-point framework

                if (result)
                {
                    Console.WriteLine("Property satisfied: ");
                }
                else
                {
                    Console.WriteLine("Property unsatisfied in k rounds: ");
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


        public Boolean boundedModelCheck(int N, int K, Expr predicate)
        {
            Boolean satisfied = false;
            Boolean terminate = false;
            Model model;
            Expr[] core;

            AHybridAutomaton h = this._has.First();

            Stack<Expr> previousStates = new Stack<Expr>();
            Expr predicatek = z3.MkFalse();
            Expr init = h.Initial;
            z3.unprimeAllVariables(ref init, 1); // rename with 0 indexing
            previousStates.Push(init);

            // loop over bound
            for (int k = 1; k <= K && !terminate; k++)
            {
                if (previousStates.Count == 0)
                {
                    // error
                    break;
                }

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


                Expr last = previousStates.Pop();
                //todo: log all these so we can compare the sequence easily

                List<Expr> cts = makeTransitions(N, k, last);

                for (int ti = 0; ti < cts.Count; ti++)
                {
                    Expr t = cts[ti];

                    z3.unprimeAllVariables(ref t, k); // renamed with k

                    if (z3.checkTerm(t, out model, out core, true)) // only add if it's satisfiable, otherwise it's a disabled transition
                    {

                        if (model != null)
                        {
                            System.Console.WriteLine("Model for transition to be taken: \n\r\n\r");
                            System.Console.WriteLine(model.ToString());
                        }


                        //z3.unprimeAllVariables(ref t); // todo: we will in general only want to unprime the new transition for efficiency (e.g., only the new piece has primed variables, so we don't want to have to walk the whole data structure to do this)
                        previousStates.Push(t);

                        Expr claim = z3.MkAnd((BoolExpr)t, (BoolExpr)predicatek);

                        // intersected with predicate
                        if (z3.checkTerm(claim, out model, out core, true))
                        {
                            satisfied = true;
                            terminate = true;
                            break;
                        }

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


            return satisfied;
        }

        public List<Expr> makeTransitions(int N, int k, Expr current)
        {
            List<Expr> transitionTerms = new List<Expr>();
            AHybridAutomaton h = this._has.First();

            foreach (ConcreteLocation l in h.Locations)
            {
                foreach (var t in l.Transitions)
                {
                    Expr currentWithTransition = current;

                    List<Expr> bound = new List<Expr>();
                    //Expr hidx = z3.MkConst("h" + k.ToString(), Controller.Instance.IndexType);
                    Expr hidx = z3.MkIntConst("h" + k.ToString());
                    bound.Add(hidx);

                    currentWithTransition = z3.MkAnd((BoolExpr)currentWithTransition, (BoolExpr)this.makeTransitionTerm(t, l, hidx));

                    currentWithTransition = z3.MkExists(bound.ToArray(), currentWithTransition);

                    transitionTerms.Add(currentWithTransition);
                }
            }
            return transitionTerms;
        }

        /**
         * Generate a specification of N (for a fixed natural number) automata for Phaver
         */
        public String outputPhaverN(uint N)
        {
            String spec = "";
            String tmp = "";

            ConcreteHybridAutomaton h = this._has.First();

            outmode mode = outmode.MODE_PHAVER;

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

            switch (mode) {
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

            spec += "REACH_USE_CONVEX_HULL = false; // not possible because of global variables" + newline +
                    "REACH_MAX_ITER = 0; " + newline +
                    "REACH_USE_BBOX = false;" + newline +
                    //"USE_HIOA_AUTOMATA = true;" + newline +
                    "COMPOSE_USE_CONVEX_HULL_FOR_REACH = false;" + newline +
                    "COMPOSE_WITH_REACH_MIN = true;" + newline +
                    "CHEAP_CONTAIN_RETURN_OTHERS = false;" + newline + newline;

            // global constants
            if (Controller.Instance.Params.Count > 0)
            {
                foreach (var p in Controller.Instance.Params)
                {
                    spec += p.Key + " := ";
                    if (Controller.Instance.ParamsAssumps.ContainsKey(p.Key))
                    {
                        spec += z3.ToStringFormatted(Controller.Instance.ParamsAssumps[p.Key].Args[1], controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true);
                        // TODO: HACK, ASSUMES ASSUMPTION IS OF THE FORM: PARAMNAME RELATION PARAMVALUE, e.g., N == 3
                    }
                    else
                    {
                        spec += "1";
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

                foreach (var v in h.Variables)
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
                if (h.Variables.Count > 0)
                {
                    spec += out_var_contr + " " + out_separator + " ";
                    foreach (var v in h.Variables)
                    {
                        spec += v.Name + "_" + i.ToString() + ",";
                    }
                    spec = spec.Substring(0, spec.Length - 1) + out_endline + newline;
                }

                // input variables for A_i: globals or universal guards
                if (this.Variables.Count > 0 || (hasUguard && N >= 2))
                {
                    spec += out_var_input + " " + out_separator + " ";

                    if (this.Variables.Count > 0)
                    {
                        foreach (var v in this.Variables) // globals
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
                        tmp = z3.ToStringFormatted(l.Invariant, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true);
                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                        spec += tmp;
                        spec += " & ";
                    }
/*
                    if (l.Stop != null)
                    {
                        // needs to be closure of negation... switch based on strict / nonstrict cases, but how to do in general?
                        tmp = z3.ToStringFormatted( z3.MkNot((BoolExpr)l.Stop), controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true);
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
                                    if (t.Guard != null)
                                    {
                                        Expr tmpt = t.Guard;
                                        Expr indexConst = z3.MkNumeral(i, Controller.Instance.IndexType);
                                        tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                        tmp = z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        spec += tmp;
                                        spec += " & ";
                                    }
                                    if (l.Invariant != null)
                                    {
                                        Expr tmpt = l.Invariant;
                                        Expr indexConst = z3.MkNumeral(i, Controller.Instance.IndexType);
                                        tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                        tmp = z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        spec += tmp;
                                        spec += " & ";
                                    }

                                    if (t.UGuard != null & N >= 2)
                                    {
                                        Expr indexConst = z3.MkNumeral(i, Controller.Instance.IndexType);

                                        tmp = "";
                                        for (uint j = 1; j <= N; j++)
                                        {
                                            if (i != j)
                                            {
                                                Expr tmpt = t.UGuard;
                                                Expr jIndexConst = z3.MkNumeral(j, Controller.Instance.IndexType);
                                                tmpt = tmpt.Substitute(Controller.Instance.Indices["j"], jIndexConst); // replace j by j value
                                                tmp += "(" + z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true) + ")"; // todo: format appropriately
                                                

                                                if (hasPointer)
                                                {
                                                    foreach (var v in h.Variables)
                                                    {
                                                        if (v.Type == Variable.VarType.index)
                                                        {
                                                            tmp = tmp.Replace("[" + v.Name + "[" + i.ToString() + "]]", "_" + j.ToString() + " & " + v.Name + "[" + i.ToString() + "] == j" ); // replace p[i] with j's actually index, e.g., x[p[i]] -> x_j /\ p[i] = j
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
                                        Expr indexConst = z3.MkNumeral(i, Controller.Instance.IndexType);
                                        tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                        tmp = "!(" + z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver) + ")"; // todo: format appropriately
                                        tmp = tmp.Replace("[i]", "_" + i.ToString());
                                        tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                        spec += tmp + " & ";
                                    }*/
                                    spec = spec.Substring(0, spec.Length - " & ".Length);
                                }

                                string synclab =  l.Label + ns.Label + i.ToString(); // unique label for all

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
                                    Expr indexConst = z3.MkNumeral(i, Controller.Instance.IndexType);
                                    tmpt = tmpt.Substitute(Controller.Instance.Indices["i"], indexConst); // replace i with actual number i (e.g., i by 1, i by 2, etc)
                                    tmp = z3.ToStringFormatted(tmpt, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver); // todo: format appropriately
                                    tmp = tmp.Replace("[i]", "_" + i.ToString());
                                    tmp = tmp.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                                    IList<Variable> globals = new List<Variable>();
                                    IList<Variable> locals = new List<Variable>();

                                    // TODO: REFACTOR NEXT TO TRANSITION CONSTRUCTOR AND ADD A LIST OF LOCAL/GLOBAL VARIABLE NAMES RESET IN THAT TRANSITION
                                    // find globals reset in t.Reset
                                    foreach (var v in this.Variables)
                                    {
                                        if (z3.findTerm(t.Reset, Controller.Instance.GlobalVariablesPrimed[v.Name], true)) // todo: add accessor in this.Variables for the expression...
                                        {
                                            globalSyncLabels.Add(synclab);
                                            continue;
                                        }
                                        else
                                        {
                                            globals.Add(v); // set identity
                                        }
                                    }
                                    globalSyncLabelsToResetGlobals.Add(synclab, globals); // add variables for identity
                                    // find locals reset in t.Reset
                                    foreach (var v in h.Variables)
                                    {
                                        if (z3.findTerm(t.Reset, Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>(v.Name + Controller.PRIME_SUFFIX, "i")], true)) // todo: add accessor in this.Variables for the expression...
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
                                    spec += " do {" + makePhaverIdentity(this.Variables, h.Variables, i) + "} ";
                                } // end reset
                                spec += " goto " + ns.Label + out_endline + newline;
                            }
                        }

                        // add self-loop (tau) transition; must have identity on all local variables (or it will introduce conservative non-determinism, which may lead to violation of properties)
                        spec += "\t when true sync tau do {" + makePhaverIdentity(this.Variables, h.Variables, i) + "} goto " + l.Label + ";" + newline;
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
                        spec += l.Label + " & "; // todo: assumes only one
                    }
                }


                if (Controller.Instance.IndexedVariables.Count == 0)
                {
                    tmp = "True";
                }
                else
                {
                    Expr tmpi = h.Initial;
                    Expr iConst = z3.MkNumeral(i, Controller.Instance.IndexType);
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

                    tmp = z3.ToStringFormatted(tmpi, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                    tmp = tmp.Replace("[i]", "_" + i.ToString());
                    tmp = tmp.Replace("[#0]", "_" + i.ToString()); // z3 3.2 format
                    tmp = tmp.Replace("[(:var 0)]", "_" + i.ToString()); // z3 4.0 format
                }
                spec += tmp;
                
                // STARL STUFF
                //spec += "x_" + i + " >= " + (x0 - delta_init) + " & x_" + i + " <= " + (x0 + delta_init) + " & y_" + i + " >= " + (y0 - delta_init) + " & y_" + i + " <= " + (y0 + delta_init);

                spec += ";" + newline + newline;

                // todo next: generalize
                //spec += " rem & True;" + newline + newline;
                spec += "end" + newline + newline;
            }

            // create global/shared variable automaton (need to do after local automaton creation to get appropriate sync labels)
            if (this.Variables.Count > 0)
            {
                spec += out_automaton + " global" + newline;

                spec += out_var_contr + " " + out_separator + " ";
                foreach (var v in this.Variables) // globals (controlled by global automaton)
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

                foreach (var v in this.Variables)
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

                spec += "\t when True sync tau do { " + makePhaverIdentity(this.Variables, new List<Variable>(), 0)  + " } goto default;" + newline; // note identity here over globals only (e.g., g' == g, no x[i]' == x[i])

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

                Expr tmpi = h.Initial;
                tmpi = tmpi.Args[0].Args[1]; // assumes (forall i ...) and GLOBAL
                String gitmp = z3.ToStringFormatted(tmpi, controller.smt.z3.Z3Wrapper.PrintFormatMode.phaver, true); // todo: format appropriately
                spec += "initially default & " + gitmp + ";" + newline + newline;

                spec += "end" + newline + newline;
            }

            spec += "sys = ";
            if (this.Variables.Count > 0)
            {
                spec += " global & ";
            }

            for (int i = 1; i <= N; i++)
            {
                spec += " agent" + i.ToString() + " & ";
            }
            spec = spec.Substring(0, spec.Length - 3);
            spec += ";" + newline + newline;
            spec += "sys.print(\"system/" + h.Name + "_N=" + Controller.Instance.IndexNValue + ".csys" + "\", 0);" + newline;

            spec += "reg = sys.reachable;" + newline;

            spec += "reg.print(\"reach/" + h.Name + "_N=" + Controller.Instance.IndexNValue + ".reach" + "\", 0);" + newline;

            string globalNames = ","; // start with comma
            foreach (var v in this.Variables)
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
            /*
            spec += "forbidden = sys.{";
            for (uint i = 1; i <= N; i++)
            {
                for (uint j = i + 1; j <= N; j++)
                {
                    spec += "$~" + makeBadString("crit", i, j, N) + " & True," + newline; // TODO: set a bad bit on states in input file?
                }
            }
            spec = spec.Substring(0, spec.Length - 2) + "};" + newline;
             */
/*
 * forbidden=sys.{
	$~CS~CS~$~$~$ & True ,
	$~$~CS~CS~$~$ & True ,
	$~$~$~CS~CS~$ & True ,
	$~$~$~$~CS~CS & True 
	};
 */
            /*
            spec += "reg.intersection_assign(forbidden);" + newline;
            spec += "echo \"\";" + newline;
            spec += "echo \"Reachable forbidden states:\";" + newline;
            spec += "reg.print(\"" + h.Name + "_ii_reach_bad\", 0);" + newline;
            spec += "echo \"\";" + newline;
            spec += "echo \"Reachable forbidden states empty?\";" + newline;
            spec += "reg.is_empty;" + newline;
             */

            return spec;
        }

        /**
         * Return phaver identity for tau transitions
         */
        String makePhaverIdentity(IList<Variable> globals, IList<Variable> locals, int id)
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


        String makeBadString(String statename, uint i, uint j, uint N)
        {
            String s = "";
            for (uint ti = 1; ti <= N; ti++)
            {
                if (ti == i || ti == j)
                {
                    s += "crit~";
                }
                else
                {
                    s += "$~";
                }
            }
            s = s.Substring(0, s.Length - 1);
            return s;
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