using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;
using passel.controller.output;
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

        public Dictionary<Tuple<String, uint>, Expr> GlobalReachValues = new Dictionary<Tuple<string, uint>, Expr>();

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
        public void removeDuplicateProperties(uint longCheck)
        {
            this.Properties = this.Properties.Distinct().ToList();
            this.Properties = this.Properties.GroupBy(p1 => p1.Formula).Select(same => same.First()).ToList();
            this.Properties = this.Properties.GroupBy(p1 => p1.Formula.ToString()).Select(same => same.First()).ToList();

            // todo: use distinct as in previous line combined with comparer that looks at Property.Formula

            int c = this.Properties.Count;
            for (int i = 0; i < c; i++)
            {
                // remove unsatisfiables
                if (longCheck >= 1)
                {
                    Controller.Instance.Z3.slvr.Push();
                    Model m;
                    Expr[] core;
                    // if assertion is unsatisfiable already, it obviously can't be an invariant
                    if (!Controller.Instance.Z3.checkTerm(this.Properties[i].Formula, out m, out core))
                    {
                        System.Console.WriteLine("REMOVING PROPERTY, EQUIVALENT TO FALSE\n\r");
                        this.Properties.RemoveAt(i);
                        c = this.Properties.Count; // update count
                        i--;
                    }
                    Controller.Instance.Z3.slvr.Pop();
                }

                // remove duplicates by formulas
                if (longCheck >= 2)
                {
                    for (int j = 0; j < c; j++)
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
                            i--;
                            j--;
                        }
                        Controller.Instance.Z3.slvr.Pop(); // restore original context
                    }
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
         * 
         * shortCircuit: if true, will stop check a potential invariant after the first transition/trajectory violation (for improved runtime);
         *               setting to false is useful for manually proving properties (e.g., by analyzing the counterexample)
         */
        public void checkInductiveInvariants(bool shortCircuit)
        {
            if (this._has == null)
            {
                return;
            }
            ConcreteHybridAutomaton h = this._has.First(); // assume only one ha
            bool iinv = true;
            bool subpart = false;
            bool restart = true;
            int proveCount = 0;
            int property_idx = 0;
            int proofPass = -1;
            int loops = 0;

            //z3.Assumptions.RemoveAll(a => a.IsQuantifier);

            this.Properties.RemoveAll(ptmp => ptmp.Status == StatusTypes.toDelete); // remove all useless properties
            this.removeDuplicateProperties(1);

            this.z3.slvr.Push();
            this.z3.slvr.Assert(this.z3.Assumptions.ToArray()); // assert all the data-type assumptions
            this.z3.slvr.Assert(this.z3.AssumptionsUniversal.ToArray()); // assert all the data-type assumptions

            Debug.Write("Attempting to prove the following " + this.Properties.Count.ToString() + " properties as inductive invariants: \n\r", Debug.VERBOSE_STEPS);
            foreach (Property pi in this.Properties)
            {
                Debug.Write(pi.Formula.ToString() + "\n\r", Debug.VERBOSE_STEPS);
                Debug.Write(pi.Post.ToString() + "\n\r", Debug.VERBOSE_ALL);
            }
            Debug.Write("End property list\n\r", Debug.VERBOSE_STEPS);

            Property p = null;

            Debug.Write("STATUS: starting inductive invariance proofs for proof iteration " + proofPass.ToString(), Debug.VERBOSE_STEPS);

            while (true)
            { 
                // termination condition: no restart and on the last property (from last iteration, before incrementing)
                if (!restart && property_idx == this.Properties.Count && this.Properties[property_idx-1].Status != StatusTypes.toProcess)
                {
                    break;
                }

                // all inductive invariants
                if (shortCircuit && (this.Properties.FindAll(pv => pv.SourceType == SourceTypes.user).All(pa => pa.Status == StatusTypes.inductiveInvariant)))
                {
                    Debug.Write("STATUS: all user supplied properties proved, breaking out of loop", Debug.MINIMAL);
                    break;
                }

                // only restart after we go through the whole list of properties (worst case behavior is the same, but on average this seems better)
                if ((restart && property_idx == this.Properties.Count) || loops <= 0)
                {
                    p = null;
                    proofPass++;
                    Debug.Write("STATUS: starting inductive invariance proofs for proof iteration " + proofPass.ToString(), Debug.VERBOSE_STEPS);
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

                    if (this.Properties.Any(ptmp => ptmp.Status == StatusTypes.inductiveInvariant))
                    {
                        Debug.Write("\n\rSTATUS: Properties proved and used as assumption lemmas: \n\r\n\r", Debug.VERBOSE_STEPS);
                    }

                    foreach (var ptmp in this.Properties)
                    {
                        if (ptmp.Status == StatusTypes.inductiveInvariant)
                        {
                            Debug.Write(ptmp.Formula.ToString() + "\n\r\n\r", Debug.VERBOSE_STEPS);
                        }

                        if (ptmp.Status == StatusTypes.inductive)
                        {
                            foreach (var pt in ptmp.InductiveInvariants)
                            {
                                Debug.Write(pt.ToString() + "\n\r\n\r", Debug.VERBOSE_STEPS);
                            }
                        }
                    }

                    z3.slvr.Push(); // PUSH1_POP1
                    z3.slvr.Check();
                    Expr[] a = z3.slvr.Assertions;
                    System.Console.WriteLine("\n\r\n\rSTATUS: ASSUMPTIONS: \n\r" + z3.ExprArrayToString(a) + "\n\r\n\r");

                    Status ca = z3.slvr.Check();
                    if (ca == Status.UNKNOWN || ca == Status.UNSATISFIABLE)
                    {
                        Debug.Write("WARNING: basic assumptions on data types, indices, etc. cannot be satisfied!", Debug.MINIMAL);
                        //throw new Exception("ERROR: basic assumptions on data types, indices, etc. cannot be satisfied!");
                    }

                    try
                    {
                        if (z3.slvr.Model != null)
                        {
                            Debug.Write("Model for basic assumptions: \n\r\n\r", Debug.VERBOSE_STEPS);
                            Debug.Write(z3.slvr.Model.ToString(), Debug.VERBOSE_STEPS);
                        }
                        if (z3.slvr.UnsatCore != null)
                        {
                            Debug.Write("Unsat core:\n\r", Debug.VERBOSE_TERMS);
                            foreach (Expr c in z3.slvr.UnsatCore)
                            {
                                Debug.Write(c.ToString(), Debug.VERBOSE_TERMS);
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

                Debug.Write("STATUS: starting inductive invariance proof for iteration " + proofPass.ToString() + ", property " + property_idx + "/" + (this.Properties.Count-1), Debug.VERBOSE_STEPS);

                p = this._properties[property_idx];
                property_idx++; // increment after read

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

                //proveCount = (int)(p.TrajectoryProved ? 1 : 0) + p.TransitionsProved.Count + (int)(p.InitialProved ? 1 : 0);
                proveCount = 0;
                subpart = false;
                iinv = true; // reset invariant shortcircuit var
                // todo next: switch , Controller.Instance.IndexType
                Expr hidx = z3.MkIntConst("h"); // h is the process making transitions
                List<Transition> tViolate = new List<Transition>(); // list of transitions that violate invariant

                Model model = null;
                Expr[] core = null;

                String tmp_stat;
                BoolExpr claimInit = z3.MkImplies((BoolExpr)h.Initial, (BoolExpr)p.Formula);
                // initiation (inductive invariance): if disproved, set as not being inductive invariant
                if (!p.InitialProved)
                {
                    if (!z3.proveTerm(claimInit, out model, out core, out tmp_stat))
                    {
                        Debug.Write("STATUS: initial states violated potential invariant", Debug.VERBOSE_STEPS);

                        p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claimInit)); // TODO: fix model generation

                        iinv = false;
                        p.Status = StatusTypes.disproved;
                        if (core != null)
                        {
                            Debug.Write("Unsat core:\n\r", Debug.VERBOSE_TERMS);
                            foreach (Expr c in core)
                            {
                                Debug.Write(c.ToString(), Debug.VERBOSE_TERMS);
                            }
                            core = null;
                        }
                    }
                    else
                    {
                        proveCount++;
                        p.InitialProved = true; // don't do again
                    }
                }

                if (iinv || !shortCircuit)
                {
                    //List<BoolExpr> discreteall = new List<BoolExpr>(); // conjunction of all possible locations for discrete transitions
                    List<BoolExpr> timeall = new List<BoolExpr>(); // conjunction of all possible locations for time transition

                    // global discrete transitions
                    foreach (var t in this.Transitions)
                    {
                        // break if some other already not invariant, OR if this property has already established this transition as an inductive invariant (e.g., in an earlier proof iteration)
                        if ((!iinv && shortCircuit) || p.TransitionsProved.Contains(t))
                        {
                            break;
                        }
                        Expr inductiveInvariant = p.Formula;

                        //inductiveInvariant = z3.MkAnd((BoolExpr)inductiveInvariant, (BoolExpr)t.TransitionTermGlobal);
                        Expr hidxinner = z3.MkIntConst("h");
                        Expr transitionTerm = t.makeTransitionTerm(null, hidxinner);
                        inductiveInvariant = z3.MkAnd((BoolExpr)inductiveInvariant, (BoolExpr)transitionTerm);

                        // alternative next, get the body and recreate
                        //Quantifier orig = inductiveInvariant.GetQuantifier();
                        //inductiveInvariant = inductiveInvariant.GetQuantifier().Body & z3.MkExists(0, bound.ToArray(), null, locInvariantAnd);
                        //inductiveInvariant = z3.MkForall(orig.Weight, null, orig.Sorts, orig.Names, inductiveInvariant);

                        //if (z3.checkTerm(inductiveInvariant, out model, out core, true)) // only check enabled transitions
                        if (iinv || !shortCircuit)
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

                            Debug.Write("\n\r<><><><><> INDUCTIVE INVARIANT START\n\r\n\r", Debug.VERBOSE_ALL);
                            Debug.Write(claim.ToString() + "\n\r\n\r", Debug.VERBOSE_ALL);
                            //if (z3.slvr.Model != null)
                            //{
                            //    Console.WriteLine(z3.slvr.Model.ToString());
                            //}
                            Debug.Write("\n\r<><><><><> INDUCTIVE INVARIANT END\n\r\n\r", Debug.VERBOSE_TERMS);

                            //z3.Push();
                            //z3.AssertCnstr(inductiveInvariant);
                            //claim = z3.Simplify(claim);

                            //if (z3.proveTerm(p.Post, out model, out core, out tmp_stat, true))
                            if (z3.proveTerm(claim, out model, out core, out tmp_stat))
                            {
                                p.Statistics.Add(tmp_stat);
                                if (core != null)
                                {
                                    Debug.Write("Unsat core:\n\r", Debug.VERBOSE_TERMS);
                                    foreach (Expr c in core)
                                    {
                                        Debug.Write(c.ToString(), Debug.VERBOSE_TERMS);
                                    }
                                    core = null;
                                }
                                // proved inductive invariant (for this transition)
                                //subpart = true;
                                proveCount++;
                                p.TransitionsProved.Add(t);
                            }
                            else
                            {
                                p.Statistics.Add(tmp_stat);
                                iinv = false;
                                tViolate.Add(t);
                                p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claim)); // TODO: fix model generation
                                //p.Counterexamples.Add(new Counterexample(null, claim)); // TODO: fix model generation
                            }
                            //z3.Pop();
                            p.addInductiveInvariant(claim);
                        }

                    } // end global discrete actions

                    /*
                    int numtrans = 0;
                    int numtransall = 0;
                    List<Transition> alltrans = new List<Transition>();
                    foreach (ConcreteLocation l in h.Locations)
                    {
                        foreach (var t in l.Transitions)
                        {
                            alltrans.Add(t);
                            if (p.TransitionsProved.Contains(t))
                            {
                                numtrans++;
                            }
                            numtransall++;
                        }
                    }

                    if (numtrans > 0 && numtrans != numtransall)
                    {
                        Console.WriteLine("Warning: skipped transition");
                        List<Transition> test = new List<Transition>();
                        test = p.TransitionsProved;
                        test.Union(alltrans);
                        alltrans = alltrans.Distinct().ToList();
                    }*/

                    foreach (ConcreteLocation l in h.Locations)
                    {
                        foreach (var t in l.Transitions)
                        {
                            //if ((!iinv && shortCircuit) || (p.TransitionsProved.Contains(t)))
                            if ((!iinv && shortCircuit))
                            {
                                break;
                            }
                            if ((p.TransitionsProved.Any(obj => obj.TransitionTerm == t.TransitionTerm)))
                            {
                                //Console.WriteLine("Skipped transition already done");
                                continue; // NOT BREAK
                            }
                            Expr inductiveInvariant = p.Formula;

                            // todo next: switch index type if not int
                            //Expr hidxinner = z3.MkConst("h", Controller.Instance.IndexType);
                            Expr hidxinner = z3.MkIntConst("h");
                            Expr transitionTerm = t.makeTransitionTerm(l, hidxinner);
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
                            if (iinv || !shortCircuit)
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


                                Debug.Write("\n\r<><><><><> INDUCTIVE INVARIANT START\n\r\n\r", Debug.VERBOSE_ALL);
                                Debug.Write(claim.ToString() + "\n\r\n\r", Debug.VERBOSE_ALL);
                                //if (z3.slvr.Model != null)
                                //{
                                //    Console.WriteLine(z3.slvr.Model.ToString());
                                //}
                                Debug.Write("\n\r<><><><><> INDUCTIVE INVARIANT END\n\r\n\r", Debug.VERBOSE_ALL);

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

                                if (z3.proveTerm(p.Post, out model, out core, out tmp_stat))
                                {
                                    p.Statistics.Add(tmp_stat);
                                    if (core != null)
                                    {
                                        Debug.Write("Unsat core:\n\r", Debug.VERBOSE_TERMS);
                                        foreach (Expr c in core)
                                        {
                                            Debug.Write(c.ToString(), Debug.VERBOSE_TERMS);
                                        }
                                        core = null;
                                    }
                                    // proved inductive invariant (for this transition)
                                    //subpart = true;
                                    proveCount++;
                                    p.TransitionsProved.Add(t);
                                }
                                else
                                {
                                    p.Statistics.Add(tmp_stat);
                                    iinv = false;
                                    tViolate.Add(t);
                                    p.Counterexamples.Add(new Counterexample(z3.slvr.Model, claim)); // TODO: FIGURE OUT WHY MODEL GENERATION DOESN'T WORK WHEN USING A TACTIC-BASED SOLVER
                                    //p.Counterexamples.Add(new Counterexample(null, claim)); // TODO: FIGURE OUT WHY MODEL GENERATION DOESN'T WORK WHEN USING A TACTIC-BASED SOLVER
                                }
                                z3.slvr.Pop();

                                p.addInductiveInvariant(claim);
                            }
                        } // end discrete actions
                    }

                    // start continuous trajectories
                    if ((iinv || !shortCircuit) && !p.TrajectoryProved && h.Variables.Any(v => v.UpdateType == Variable.VarUpdateType.continuous))
                    {
                        // start continuous transition (we add a a part for each location as we iterate over them)
                        //hidx = z3.MkConst("h", Controller.Instance.IndexType); // make fresh
                        hidx = z3.MkIntConst("h");

                        Expr timeii = this.makeFlowsAll(h, p.Formula);
                        p.addInductiveInvariant(timeii);

                        //if (z3.checkTerm(timeii, out model, out core, true))
                        //if (z3.proveTerm(inductiveInvariant, out model, out core, true))
                        if (true)
                        {
                            timeii = z3.MkImplies((BoolExpr)timeii, (BoolExpr)p.Post);

                            //timeii = z3.MkExists(Controller.Instance.ExistentialConstants.Values.ToArray(), timeii); // todo: only do this for termination properties

                            if (z3.proveTerm(timeii, out model, out core, out tmp_stat))
                            {
                                p.Statistics.Add(tmp_stat);
                                // proved inductive invariant (for this location of the timed transition)
                                if (core != null)
                                {
                                    Debug.Write("Unsat core:\n\r", Debug.VERBOSE_TERMS);
                                    foreach (Expr c in core)
                                    {
                                        Debug.Write(c.ToString(), Debug.VERBOSE_TERMS);
                                    }
                                    core = null;
                                }
                                proveCount++;
                                p.TrajectoryProved = true; // don't check again
                            }
                            else
                            {
                                p.Statistics.Add(tmp_stat);
                                iinv = false;
                                p.Counterexamples.Add(new Counterexample(z3.slvr.Model, timeii)); // TODO: fix model generation
                                //p.Counterexamples.Add(new Counterexample(null, timeii)); // TODO: fix model generation
                            }
                        }
                    } // end continuous flows
                    //}
                }

                if (proveCount == 0)
                {
                    iinv = false;
                }

                // property is not an inductive invariant
                if (!iinv)
                {
                    Debug.Write("STATUS: Property was NOT an inductive invariant!", Debug.VERBOSE_STEPS);
                    Debug.Write("Property checked was: \n\r" + p.Formula.ToString(), Debug.VERBOSE_TERMS);
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    Debug.Write("STATUS: Property was an inductive invariant!", Debug.VERBOSE_STEPS);
                    Debug.Write("Property checked was: \n\r" + p.Formula.ToString(), Debug.VERBOSE_TERMS);
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
                /*if (!inv)
                {
                    //Console.WriteLine("\n\r\n\rProperty was NOT inductive!");
                    //Console.WriteLine("Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    // only do this for non-invariants
                    if (!iinv)
                    {
                        //Console.WriteLine("\n\r\n\rProperty was inductive!");
                        //Console.WriteLine("Property checked was: \n\r" + p.Formula.ToString());
                        p.Status = StatusTypes.inductive;

                        //z3.AssertCnstr(p.Formula); // probably don't want to assert this, as this would require it to be invariant

                        p.InductiveFormula = z3.MkOr((BoolExpr[])p.InductiveInvariants.ToArray());
                    }
                }*/
                Controller.Instance.TimerStats.Stop();

                // once we assert a property as a lemma, we go back to all other formulas and attempt to reprove them so that the order of the lemma assertions does not matter
                if (subpart || iinv)
                {
                    restart = true;

                    // edge case if last lemma is disproved
                    if (property_idx == this.Properties.Count)
                    {
                        property_idx = 0;
                    }
                }


                //String quantInstStr = p.Statistics[p.Statistics.Count-1];
                //quantInstStr = quantInstStr.Substring(quantInstStr.IndexOf("\nquant instantiations:")).Trim(); // use newline: there is another statistic called "lazy quantifier instantiations:", so we don't want to match that (otherwise get wrong or even negative values)
                //quantInstStr = quantInstStr.Split(':')[1].Split('\n')[0];
                //p.QuantInstantiations = int.Parse(quantInstStr) - QuantInstantiationsLast;
                //
                p.Time = Controller.Instance.TimerStats.Elapsed;
                loops++;
            }

            Debug.Write("\n\rUNPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r", Debug.VERBOSE_STEPS);
            foreach (Property pi in this.Properties)
            {
                if (pi.Status != StatusTypes.inductiveInvariant)
                {
                    Debug.Write("PROPERTY UNPROVED =====================================================================\n\r", Debug.VERBOSE_STEPS);
                    Debug.Write(pi.Formula.ToString() + "\n\r\n\r", Debug.VERBOSE_STEPS);

                    Debug.Write("Time: " + String.Format("{0}", pi.Time.TotalSeconds) + "\n\r", Debug.VERBOSE_STEPS);

                    Debug.Write("REASONS (counterexample / trace):\n\r", Debug.VERBOSE_STEPS);
                    foreach (Counterexample ce in pi.Counterexamples)
                    {
                        if (ce.Model != null)
                        {
                            System.Console.WriteLine("Counterexample model:\n\r");
                            System.Console.WriteLine(ce.Model.ToString());

                            System.Console.WriteLine("Pre-state");
                            foreach (var v in ce.Model.ConstDecls)
                            {
                                if (!v.ToString().Contains(Controller.PRIME_SUFFIX))
                                {
                                    System.Console.WriteLine(v.Name.ToString() + " == " + ce.Model.ConstInterp(v));
                                }
                            }

                            foreach (var v in ce.Model.FuncDecls)
                            {
                                if (!v.ToString().Contains(Controller.PRIME_SUFFIX))
                                {
                                    System.Console.WriteLine(v.Name.ToString() + " == " + ce.Model.FuncInterp(v));
                                }
                            }

                            System.Console.WriteLine("\n\rPost-state");
                            foreach (var v in ce.Model.ConstDecls)
                            {
                                if (v.ToString().Contains(Controller.PRIME_SUFFIX))
                                {
                                    System.Console.WriteLine(v.Name.ToString() + " == " + ce.Model.ConstInterp(v));
                                }
                            }

                            foreach (var v in ce.Model.FuncDecls)
                            {
                                if (v.ToString().Contains(Controller.PRIME_SUFFIX))
                                {
                                    System.Console.WriteLine(v.Name.ToString() + " == " + ce.Model.FuncInterp(v));
                                }
                            }
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
                    Debug.Write("END PROPERTY UNPROVED =====================================================================\n\r\n\r", Debug.VERBOSE_STEPS);
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



            System.Console.WriteLine("UNPROVED INVARIANTS SUMMARY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            int num_dis = 0;
            foreach (Property pi in this.Properties)
            {
                if (pi.Status != StatusTypes.inductiveInvariant)
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
            System.Console.WriteLine("Unproved: " + num_dis.ToString());
            System.Console.WriteLine("Invariant: " + num_inv.ToString() + "\n\r");
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
            this.z3.slvr.Pop(); // remove assumptions
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="h"></param>
        /// <param name="prestate"></param>
        /// <param name="paramsList"></param>
        /// <returns></returns>
        public Expr makeFlowsAll(AHybridAutomaton h, Expr prestate, params uint[] paramsList)
        {
            uint N = 0;
            uint k = 0;
            if (paramsList != null && paramsList.Length > 0)
            {
                N = paramsList[0];
                if (paramsList.Length > 1)
                {
                    k = paramsList[1];
                }
            }

            Expr hidx = z3.MkIntConst("h");

            List<BoolExpr> timeall = new List<BoolExpr>();
            Expr timeii = prestate;
            foreach (Location l in h.Locations)
            {
                List<BoolExpr> exprlist = new List<BoolExpr>();
                Expr expr = null;
                ArithExpr t1 = (ArithExpr)z3.MkRealConst("t_1"); // existential
                ArithExpr t2 = (ArithExpr)z3.MkRealConst("t_2"); // universal

                ArithExpr delta = null;

                if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                {
                    delta = (ArithExpr)z3.MkRealConst("delta"); // existential (for rectangular dynamics)
                }

                exprlist.AddRange(l.MakeFlow(hidx, t1, t2, delta));

                List<Expr> bt = new List<Expr>();
                //hidx = z3.MkConst("h", Controller.Instance.IndexType);
                bt.Add(hidx);

                if (Controller.Instance.TimeOption == Controller.TimeOptionType.separated)
                {
                    exprlist.Add((BoolExpr)l.StatePredicate); // control location, e.g., q[h] == 2
                }

                if (exprlist.Count > 1)
                {
                    expr = z3.MkAnd(exprlist.ToArray());
                }
                else if (exprlist.Count == 1)
                {
                    expr = exprlist[0];
                }
                else
                {
                    //throw new Exception("ERROR: poorly formatted flow condition.");
                    // no flow conditions at all: do not take time transitions
                    continue;
                }

                if (Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction)
                {
                    expr = z3.MkImplies((BoolExpr)l.StatePredicate, (BoolExpr)expr); // control location, e.g., q[h] == 2 implies (inv, guard, flow, etc.)
                }

                expr = expr.Substitute(Controller.Instance.Indices["i"], hidx); // replace i by h

                // if we haven't yet add every location's invariant, keep adding them on
                if (Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction && timeall.Count <= h.Locations.Count)
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

                Expr tid = Controller.Instance.Sys.timeIdentity(hidx);

                // for bounded-model checking: do the state rename outside the quantifiers
                if (N > 0 || k > 0)
                {
                    //z3.unprimeAllVariables(ref expr, k);
                    //z3.unprimeAllVariables(ref tid, k);

                    expr = replacePrimeReach(expr, hidx, N, k);
                    tid = replacePrimeReach(tid, hidx, N, k);
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

                if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                {
                    expr = z3.MkExists(new Expr[] { delta }, expr);
                }

                if (N > 0 || k > 0)
                {
                    // todo: repeat copies
                    expr = z3.MkAnd((BoolExpr)expr, (BoolExpr)tid);
                }
                else
                {
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
                }

                switch (Controller.Instance.ExistsOption)
                {
                    case Controller.ExistsOptionType.and:
                        expr = z3.MkExists(new Expr[] { t1 }, z3.MkAnd(z3.MkGt(t1, Controller.Instance.RealZero), (BoolExpr)expr)); // broken with invariants if using implies
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

        public Expr replacePrimeReach(Expr expr, Expr idx, uint N, uint k)
        {
            List<BoolExpr> transAll = new List<BoolExpr>();
            // expand quantifier manually
            BoolExpr copy = (BoolExpr)Controller.Instance.Z3.copyExpr(expr);
            for (uint i = 1; i <= N; i++)
            {
                Expr numidx = Controller.Instance.Z3.MkInt(i);
                //Expr trans = locInvariantAnd.Substitute(idx, numidx); // instantiate i
                //transAll.Add(z3.MkAnd(z3.MkEq(idx, numidx), (BoolExpr)locInvariantAnd)); // simply set symbol idx = value idx
                copy = (BoolExpr)Controller.Instance.Z3.copyExpr(expr);

                foreach (var v in Controller.Instance.Sys.Variables)
                {
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.Sys.GlobalReachValues[new Tuple<string, uint>(v.Name, k)]); // substitute to constant (needed for doing q.e.)
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Name], Controller.Instance.Sys.GlobalReachValues[new Tuple<string, uint>(v.Name, k + 1)]); // substitute to constant (needed for doing q.e.)
                }

                foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables) // TODO: generalize
                {
                    //copy.Substitute(z3.MkApp(v.Value, idx), z3.MkApp(v.Value, numidx)); // substitute to function
                    //idx = Controller.Instance.Z3.MkIntConst("i");
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.IndexedVariables[new KeyValuePair<string,string>(v.Name, idx.ToString())], Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k, i)]); // substitute to constant (needed for doing q.e.)
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>(v.Name + Controller.PRIME_SUFFIX, idx.ToString())], Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k + 1, i)]); // substitute to constant (needed for doing q.e.)
                }
                copy = (BoolExpr)copy.Substitute(idx, numidx); // must be outside variable loop

                //copy = Controller.Instance.Z3.MkAnd(copy, (BoolExpr)Controller.Instance.Z3.forallIdentity(Controller.Instance.Z3.MkInt(i), globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N));
                /*
                for (uint j = 1; j <= N; j++)
                {
                    if (j == i)
                    {
                        continue;
                    }
                    foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables) // TODO: generalize
                    {
                        copy = (BoolExpr)copy.Substitute(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Z3.MkInt(j)), Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k, j)]); // substitute to constant (needed for doing q.e.)
                        copy = (BoolExpr)copy.Substitute(Controller.Instance.Z3.MkApp(v.ValuePrimed, Controller.Instance.Z3.MkInt(j)), Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k + 1, j)]); // substitute to constant (needed for doing q.e.)
                    }
                }*/
                transAll.Add(copy);
            }
            expr = Controller.Instance.Z3.MkAnd(transAll.ToArray());
            //return copy;
            return expr;
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
                                    if (f.Variable != v)
                                    {
                                        continue;
                                    }
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
                                                if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                                                {
                                                    flowInv = flowInv.Substitute(f.RectRateA, delta); // replace A from \dot{x} \in [A,B] with \delta which exists in [A,B]
                                                }
                                                tmpterm = tmpterm.Substitute(varTerm, flowInv);

                                                if (Controller.Instance.FlowOption == Controller.FlowOptionType.function)
                                                {
                                                    tmpterm = z3.MkAnd((BoolExpr)tmpterm, (BoolExpr)tmpterm.Substitute(f.RectRateA, f.RectRateB));
                                                }

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
                Expr result = boundedModelCheck(Controller.Instance.IndexNValue, 100, p.Formula); // use our own BMC
                //Boolean result = fixedpointCheck(2, 100, p.Formula); // use the Z3 provided fixed-point framework
                /*
                if (result)
                {
                    Console.WriteLine("Property satisfied: " + p.ToString());
                }
                else
                {
                    Console.WriteLine("Property unsatisfied in k rounds: " + p.ToString());
                }*/
            }
        }

        // todo: this is for the fixed point interface version
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

        public class TransitionBranch
        {
            public Expr State;
            public bool FixedPoint = false;
            public enum TransitionType { Discrete, Continuous };
            public List<uint> ProcessesMoving = new List<uint>();

            public TransitionBranch(Expr t, params uint[] processesMoving)
            {
                this.State = t;
                this.ProcessesMoving.AddRange(processesMoving);
            }
        }


        public class ReachStructure
        {
            public Expr ReachedStates = Controller.Instance.Z3.MkFalse();
            public List<TransitionBranch> TransitionSequence = new List<TransitionBranch>();
            public uint Step;
            public Expr ReachSet = Controller.Instance.Z3.MkFalse(); // collapsed reach states (all named with same sequence state for fixed-point)

            private Expr LastReachedStates;
            private Expr LastReachSet;

            public ReachStructure(Expr lastReach, uint iteration, params BoolExpr[] reached)
            {
                this.Step = iteration;
                if (reached.Length > 0)
                {
                    //this.Add(reached[0], reached.SelectMany(r => r.);
                    this.Add(reached[0]); // todo: add rest
                }
                else
                {
                    this.Add(Controller.Instance.Z3.MkFalse());
                    this.TransitionSequence.First().FixedPoint = true;
                }
                this.ReachSet = lastReach;

                // todo: REFACTOR INTO FUNCTION
                    for (uint k = 0; k <= this.Step; k++)  // TODO: only have to do this for k-1?; TODO: cannot do it for k-1 since seq is the whole transition sequence: we need only the new delta change and then we can do it this way and it'll be much more efficient
                    {
                        foreach (var v in Controller.Instance.Sys.Variables) // TODO: global vars aren't indexed by i
                        {
                            Tuple<string, uint> id = new Tuple<string, uint>(v.Name, k);
                            this.ReachSet = (BoolExpr)this.ReachSet.Substitute(Controller.Instance.Sys.GlobalReachValues[id], Controller.Instance.GlobalVariables[v.Name]);
                        }

                        for (uint i = 1; i <= Controller.Instance.IndexNValue; i++)
                        {
                            foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
                            {
                                Tuple<string, uint, uint> id = new Tuple<string, uint, uint>(v.Name, k, i);
                                this.ReachSet = (BoolExpr)this.ReachSet.Substitute(Controller.Instance.Sys.ReachValues[id], Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, i.ToString())]);
                            }
                        }
                    }
                
            }

            /*
             * TODO
             * Finish creating this: ideally we'll just remove a node from a tree, currently would have to remove a disjunct from TransitionSequence or ReachedStates
             */
            public void Remove()
            {
                this.ReachSet = this.LastReachSet; // todo: see if this holds between iterations
                this.ReachedStates = this.LastReachedStates;
            }

            public void Add(BoolExpr seq, params BoolExpr[] reached)
            {
                this.LastReachedStates = this.ReachedStates;
                this.LastReachSet = this.ReachSet;
                // invariant ensures all states are either labeled with 0, or the most recent transition number
                //for (uint kfrom = 1; kfrom <= this.Step; k++)
                //{
                //}

                if (reached.Length == 0)
                {
                }
                else if (reached.Length == 1)
                {
                    this.ReachedStates = Controller.Instance.Z3.MkOr((BoolExpr)this.ReachedStates, reached[0]);
                }
                else
                {
                    this.ReachedStates = Controller.Instance.Z3.MkOr((BoolExpr)this.ReachedStates, Controller.Instance.Z3.MkOr(reached));
                }
                // TODO NEXT: does this do what was intended?
                Controller.Instance.Z3.unprimeAllVariablesReachability(ref this.ReachedStates, 0, this.Step); // rename all states to 0

                this.TransitionSequence.Add(new TransitionBranch(seq));

                if (reached.Length > 0)
                {
                    List<BoolExpr> rs = new List<BoolExpr>();
                    foreach (var s in reached)
                    {
                        BoolExpr stmp = s;
                        for (uint k = 0; k <= this.Step + 1; k++)  // TODO: only have to do this for k-1?; TODO: cannot do it for k-1 since reached is the whole transition sequence: we need only the new delta change and then we can do it this way and it'll be much more efficient
                        {
                            foreach (var v in Controller.Instance.Sys.Variables) // TODO: global vars aren't indexed by i
                            {
                                Tuple<string, uint> id = new Tuple<string, uint>(v.Name, k);
                                stmp = (BoolExpr)stmp.Substitute(Controller.Instance.Sys.GlobalReachValues[id], Controller.Instance.GlobalVariables[v.Name]);
                            }
                            for (uint i = 1; i <= Controller.Instance.IndexNValue; i++)
                            {
                                foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
                                {
                                    Tuple<string, uint, uint> id = new Tuple<string, uint, uint>(v.Name, k, i);
                                    stmp = (BoolExpr)stmp.Substitute(Controller.Instance.Sys.ReachValues[id], Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, i.ToString())]);
                                }
                            }
                        }
                        rs.Add(stmp);
                    }
                    rs.Add((BoolExpr)this.ReachSet); // original set
                    this.ReachSet = Controller.Instance.Z3.MkOr(rs.ToArray());
                }




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
         * 
         * K == 0 means to perform unbounded model checking to a fixed point
         */
        public Expr boundedModelCheck(uint N, uint K, Expr predicate)
        {
            Boolean satisfied = false;
            Boolean terminate = false;
            Model model;
            Expr[] core;

            // setup variables for fixed-point
            foreach (var v in this.HybridAutomata[0].Variables)
            {
                for (uint i = 1; i <= Controller.Instance.IndexNValue; i++)
                {
                    try
                    {
                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<string, string>(v.Name, i.ToString()), Controller.Instance.Z3.MkConst(v.Name + "_" + i.ToString(), v.TypeSort));
                    }
                    catch
                    {
                    }
                    try
                    {
                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<string, string>(v.Name + Controller.PRIME_SUFFIX, i.ToString()), Controller.Instance.Z3.MkConst(v.Name + Controller.PRIME_SUFFIX + "_" + i.ToString(), v.TypeSort));
                    }
                    catch
                    {
                    }
                }
            }

            Expr reachReturn = z3.MkFalse();

            AHybridAutomaton h = this._has.First();

            //pmode enum { mode_fifo, mode_lifo };

            //Stack<Expr> previousStates = new Stack<Expr>();
            //Queue<Expr> previousStates = new Queue<Expr>();
            SortedDictionary<uint, ReachStructure> previousStates = new SortedDictionary<uint, ReachStructure>();
            Expr predicatek = z3.MkFalse();
            //Expr init = h.Initial;
            Expr init;
            List<BoolExpr> initList = new List<BoolExpr>();
            this.ReachValues = new Dictionary<Tuple<string, uint, uint>, Expr>();
            this.GlobalReachValues = new Dictionary<Tuple<string, uint>, Expr>();


            // add new state variables for round k
            foreach (var v in this.Variables)
            {
                this.GlobalReachValues.Add(new Tuple<string, uint>(v.Name, 0), z3.MkConst(v.Name + (0), v.TypeSort));
                this.GlobalReachValues.Add(new Tuple<string, uint>(v.Name, 1), z3.MkConst(v.Name + (1), v.TypeSort));
            }

            foreach (var v in this.HybridAutomata[0].Variables)
            {
                for (uint i = 1; i <= N; i++)
                {
                    this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name, 0, i), z3.MkConst(v.Name + 0 + "_" + i, v.TypeSort));
                    this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name,  1, i), z3.MkConst(v.Name + ( 1) + "_" + i, v.TypeSort));
                }
            }


            init = h.makeInitialBmc(N);

            //z3.Assumptions.RemoveAll(a => a.IsQuantifier);
            this.z3.slvr.Assert(this.z3.Assumptions.ToArray()); // assert all the data-type assumptions
            this.z3.slvr.Assert(this.z3.AssumptionsUniversal.ToArray()); // assert all the data-type assumptions
            //init = z3.MkAnd((BoolExpr)init, (BoolExpr)z3.MkAnd(z3.Assumptions.ToArray()));

            z3.unprimeAllVariables(ref init, 1); // rename with 0 indexing (no primed variables, so only unprimed -> 0)

            previousStates.Add(0, new ReachStructure( (BoolExpr)init, 0, (BoolExpr)init ));

            // loop over bound
            for (uint k = 1; (k <= K || K == 0) && !terminate; k++)
            {
                Debug.Write("\n\rBMC iteration " + k.ToString(), Debug.MINIMAL);

                previousStates.Add(k, new ReachStructure(previousStates[k-1].ReachSet, k));

                // termination condition --- no further transitions enabled
                if (previousStates[k-1].TransitionSequence.Count == 0 || terminate || previousStates[k-1].TransitionSequence.All(seq => seq.FixedPoint))
                {
                    Debug.Write("REACHSET: ", Debug.MINIMAL);
                    Debug.Write(previousStates[k - 1].ReachSet.ToString(), Debug.MINIMAL);

                    reachReturn = previousStates[k - 1].ReachSet;

                    break;
                }

                uint lti = 0;
                foreach (TransitionBranch last in previousStates[k-1].TransitionSequence)
                {
                    Debug.Write("\n\rBMC iteration " + k.ToString() + "." + lti.ToString(), Debug.MINIMAL);
                    if (last.FixedPoint)
                    {
                        last.FixedPoint = true;
                        continue;
                    }

                    Expr predicatektmp = this.z3.MkNot((BoolExpr)predicate); // todo: predicates are mostly safety properties, not bad / unsafety properties, so we negate them
                    z3.unprimeAllVariables(ref predicatektmp, k); // rename with k indexing
                    predicatek = z3.MkOr((BoolExpr)predicatek, (BoolExpr)predicatektmp);

                    /*
                    // safety check
                    Expr claim = z3.MkAnd((BoolExpr)last.State, (BoolExpr)predicatek);
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
                     */

                    // add new state variables for round k
                    foreach (var v in this.Variables)
                    {
                        Tuple<string, uint> id = new Tuple<string, uint>(v.Name, k + 1);
                        if (!this.GlobalReachValues.ContainsKey(id))
                        {
                            this.GlobalReachValues.Add(id, z3.MkConst(v.Name + (k + 1), v.TypeSort));
                        }
                    }

                    // add new state variables for round k
                    foreach (var v in this.HybridAutomata[0].Variables)
                    {
                        for (uint i = 1; i <= N; i++)
                        {
                            Tuple<string, uint, uint> id = new Tuple<string, uint, uint>(v.Name, k+1, i);
                            //this.ReachValues.Add(new Tuple<string, uint, uint>(v.Name, k, i), z3.MkConst(v.Name + k + "_" + i, v.TypeSort));
                            if (!this.ReachValues.ContainsKey(id))
                            {
                                this.ReachValues.Add(id, z3.MkConst(v.Name + (k + 1) + "_" + i, v.TypeSort));
                            }
                        }
                    }

                    List<TransitionStructure> cts = new List<TransitionStructure>();
                    cts.Add(makeTimeTransition(N, k-1, last.State));
                    cts.AddRange(makeTransitions(N, k-1, last.State, 0));

                    for (int ti = 0; ti < cts.Count; ti++)
                    {
                        Debug.Write("BMC iteration " + k.ToString() + "." + lti.ToString() + "." + ti.ToString(), Debug.MINIMAL);

                        Expr t = cts[ti].PreviousWithTransition;

                        if (z3.checkTerm(t, out model, out core)) // only add if it's satisfiable, otherwise it's a disabled transition
                        {
                            if (model != null)
                            {
                                Debug.Write("Model for transition to be taken: \n\r\n\r", Debug.VERBOSE_TERMS);
                                Debug.Write(model.ToString(), Debug.VERBOSE_TERMS);
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

                            //previousStates[k].Add( (BoolExpr)t ); // TODO: add only the delta change, not the whole sequence, we don't need that
                            //previousStates[k].Add((BoolExpr)cts[ti].ResetOnly);
                            BoolExpr newstates = z3.MkTrue();
                            if (cts[ti].Trans == Transition.TimeTransition)
                            {
                                //Tactic tqe = z3.Repeat(z3.Then(z3.MkTactic("simplify"), z3.MkTactic("ctx-simplify"), z3.Repeat(z3.Then(z3.MkTactic("qe"), z3.MkTactic("elim-and"), z3.OrElse(z3.MkTactic("split-clause"), z3.MkTactic("skip")))), z3.MkTactic("simplify"), z3.MkTactic("propagate-values"), z3.MkTactic("propagate-ineqs")));
                                Tactic tqe = z3.Repeat(z3.Then(z3.MkTactic("simplify"),
                                                               z3.MkTactic("ctx-simplify"),
                                                               z3.Repeat(z3.Then(z3.MkTactic("qe"), z3.MkTactic("propagate-values"), z3.MkTactic("propagate-ineqs")))));
                                Goal g = z3.MkGoal(true);
                                //g.Assert(z3.Assumptions.ToArray()); // basic assumptions
                                g.Assert((BoolExpr)t);
                                Params p = z3.MkParams();
                                p.Add("PI_AVOID_SKOLEMS", true);
                                p.Add("PI_PULL_QUANTIFIERS", true);
                                p.Add("PI_USE_DATABASE", true);
                                ApplyResult ar = tqe.Apply(g, p);

                                ar = ar;

                                Debug.Write("After simplify:" + ar.ToString(), Debug.VERBOSE_TERMS);

                                List<BoolExpr> sgfall = new List<BoolExpr>();
                                foreach (var sgf in ar.Subgoals)
                                {
                                    sgfall.AddRange(sgf.Formulas);
                                }
                                newstates = z3.MkAnd(sgfall.ToArray());
                                previousStates[k].Add( z3.MkAnd((BoolExpr)last.State, newstates), newstates  ); 
                            }
                            else
                            {
                                BoolExpr frontier = (BoolExpr)z3.MkOr((BoolExpr)last.State, (BoolExpr)cts[ti].ResetOnly);
                                //previousStates[k].Add(frontier);
                                previousStates[k].Add((BoolExpr)t, (BoolExpr)cts[ti].Trans.MakeReset(Controller.Instance.Indices["i"], N, k));
                            }


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
                            BoolExpr fp = z3.MkImplies((BoolExpr)previousStates[k].ReachSet, (BoolExpr)previousStates[k-1].ReachSet);
                            /*Term fp = t & !last; // P and \neg B, where P is current, B is previous
                            Console.WriteLine("fixed point check:");
                            Console.WriteLine(fp.ToString());
                            String s;*/
                            String stat = null;
                            if (z3.proveTerm(fp, out model, out core, out stat)) // use true for proveterm with implies version
                            {
                                if (cts[ti].Trans == Transition.TimeTransition)
                                {
                                    foreach (var st in previousStates[k].TransitionSequence.FindAll(x => x.State == z3.MkAnd((BoolExpr)last.State, newstates)))
                                    {
                                        st.FixedPoint = true;
                                    }
                                }
                                else
                                {
                                    foreach (var st in previousStates[k].TransitionSequence.FindAll(x => x.State == t))
                                    {
                                        st.FixedPoint = true;
                                    }
                                }
                                //previousStates[k].TransitionSequence.Find(x => x.State == cts[ti].Trans.MakeReset(Controller.Instance.Indices["i"], N, k)).FixedPoint = true;
                                previousStates[k].Remove(); // reset reach set formula
                            }
                        }
                        else
                        {
                            Debug.Write("disabled transition: ", Debug.VERBOSE_TERMS);
                            Debug.Write(t.ToString(), Debug.VERBOSE_TERMS);
                        }

                    }
                    lti++;
                }
            }
            return reachReturn;
        }

        public class TransitionStructure
        {
            public Expr PreviousWithTransition;
            public Expr ResetOnly;
            public Transition Trans;
            public TransitionStructure(Expr pwt, Expr ro, Transition t)
            {
                this.PreviousWithTransition = pwt;
                this.ResetOnly = ro;
                this.Trans = t;
            }
        }

        public List<TransitionStructure> makeTransitions(uint N, uint k, Expr current, uint quant)
        {
            List<TransitionStructure> transitionTerms = new List<TransitionStructure>();
            AHybridAutomaton h = this._has.First();

            // todo: GLOBAL TRANSITIONS (not used much, only a few examples)

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

                        Expr trans = (BoolExpr)t.makeTransitionTerm(l, hidx);
                        z3.unprimeAllVariables(ref trans, k); // renamed with k

                        currentWithTransition = z3.MkAnd((BoolExpr)currentWithTransition, (BoolExpr)trans);
                        currentWithTransition = z3.MkExists(bound.ToArray(), currentWithTransition);
                        transitionTerms.Add(new TransitionStructure(currentWithTransition, trans, t));
                    }
                    else
                    {
                        Expr hidx = z3.MkIntConst("h" + k.ToString());
                        BoolExpr tt = (BoolExpr)t.makeTransitionTerm(l, hidx, N, k, quant);
                        foreach (var v in tt.Args)
                        {
                            currentWithTransition = current;
                            currentWithTransition = z3.MkAnd((BoolExpr)currentWithTransition, (BoolExpr)v);
                            z3.unprimeAllVariables(ref currentWithTransition, k); // renamed with k
                            transitionTerms.Add(new TransitionStructure(currentWithTransition, tt, t));
                        }
                    }
                }
            }
            return transitionTerms;
        }

        /**
         * Identity function for all processes not making a transition
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         */
        public Expr forallIdentity(Expr indexMakingMove, List<String> globalVariableResets, List<String> indexVariableResets, List<String> universalIndexVariableResets, Expr uguardReset, params uint[] paramsList)
        {
            uint N = 0;
            if (paramsList != null && paramsList.Length > 0)
            {
                N = paramsList[0];
            }

            List<BoolExpr> f = new List<BoolExpr>();
            List<BoolExpr> outside_forall = new List<BoolExpr>();
            List<Expr> bound = new List<Expr>();
            String idx = "j";

            bound.Add(Controller.Instance.Indices[idx]);

            // set equality on unprimed pre-state and primed post-state for all indexed variables of all other processes (those not making the move) (e.g., q[j]' == q[j])
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            if (!universalIndexVariableResets.Contains(v.Key))
                            {
                                //grab only idx
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));
                            }
                            else
                            {
                                if (uguardReset != null)
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (universalIndexVariableResets != null && !universalIndexVariableResets.Contains(v.Key))
                            {
                                //grab only idx
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));

                                // add basic universal guard
                                // TODO: CHECK IF THIS WORKS WITH RESETS
                                if (uguardReset != null && !uguardReset.ToString().Contains(Controller.PRIME_SUFFIX) && !uguardReset.ToString().Contains(Controller.PRIME_SUFFIX_PARSER))
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                            else
                            {
                                if (uguardReset != null)
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all unprimed pre-state and primed post-state of all indexed variables ***NOT APPEARING IN THE RESET*** for the process making the move (e.g., x[h]' == x[h], if x[h] is not reset)
            if (indexMakingMove != null)
            {
                if (indexVariableResets != null)
                {
                    foreach (var v in indexVariableResets)
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v], indexMakingMove)));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v], indexMakingMove)));
                                    break;
                                }
                        }
                    }
                }
            }

            if (globalVariableResets != null)
            {
                // set equality on all unprimed pre-state and primed post-tate of all global variables ***NOT APPEARING IN THE RESET*** (e.g., g' == g, if g is not reset)
                foreach (var v in globalVariableResets)
                {
                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v], Controller.Instance.GlobalVariablesPrimed[v]));
                }
            }
            List<BoolExpr> ibds = new List<BoolExpr>();
            if (Controller.Instance.IndexOption == Controller.IndexOptionType.naturalOneToN)
            {
                ibds.Add(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Indices[idx], (ArithExpr)Controller.Instance.IndexOne));
                ibds.Add(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Indices[idx], (ArithExpr)Controller.Instance.IndexN));
            }

            Expr ret;
            Expr fand = Controller.Instance.Z3.MkAnd(f.ToArray());
            if (indexMakingMove != null)
            {
                Expr distinct = Controller.Instance.Z3.MkDistinct(bound.First(), indexMakingMove);

                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.integer:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies((BoolExpr)distinct, (BoolExpr)fand));
                        break;
                    case Controller.IndexOptionType.naturalOneToN:
                        if (N == 0) // symbolic 
                        {
                            ibds.Add((BoolExpr)distinct);
                            ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd(ibds.ToArray()), (BoolExpr)fand));
                        }
                        else // expanded
                        {
                            List<BoolExpr> forallList = new List<BoolExpr>();
                            for (uint i = 1; i <= N; i++)
                            {
                                uint ihack = 0;
                                uint.TryParse(indexMakingMove.ToString(), out ihack);

                                if (i == ihack)
                                {
                                    continue;
                                }

                                // todo next: indexing checking
                                //BoolExpr fandCopy = (BoolExpr)this.MkImplies((BoolExpr)distinct, (BoolExpr)fand).Substitute(bound[0], this.MkInt(i));
                                BoolExpr fandCopy = (BoolExpr)fand.Substitute(bound[0], Controller.Instance.Z3.MkInt(i));
                                forallList.Add(fandCopy);
                            }
                            ret = Controller.Instance.Z3.MkAnd(forallList.ToArray());
                        }
                        break;
                    case Controller.IndexOptionType.enumeration:
                    default:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies((BoolExpr)distinct, (BoolExpr)fand));
                        break;
                }
            }
            else
            {
                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.integer:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), fand);
                        break;
                    case Controller.IndexOptionType.naturalOneToN:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd((BoolExpr[])ibds.ToArray()), (BoolExpr)fand));
                        break;
                    case Controller.IndexOptionType.enumeration:
                    default:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), fand); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                }
            }

            // only add the outside forall constraints if there are any
            if (outside_forall.Count > 0)
            {
                outside_forall.Add((BoolExpr)ret); // prettier printing (fewer ands)
                ret = Controller.Instance.Z3.MkAnd(outside_forall.ToArray());
            }
            return ret;
        }








                 
        /// <summary>
        /// Identity function for all processes not making a transition
        /// I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
        /// </summary>
        /// <param name="indexMakingMove"></param>
        /// <param name="globalVariableResets"></param>
        /// <param name="indexVariableResets"></param>
        /// <param name="universalIndexVariableResets"></param>
        /// <param name="uguardReset"></param>
        /// <param name="paramsList"></param>
        /// <returns></returns>
        public Expr forallIdentityPost(Expr indexMakingMove, List<String> globalVariableResets, List<String> indexVariableResets, List<String> universalIndexVariableResets, Expr uguardReset, params uint[] paramsList)
        {
            uint N = 0;
            if (paramsList != null && paramsList.Length > 0)
            {
                N = paramsList[0];
            }

            List<BoolExpr> f = new List<BoolExpr>();
            List<BoolExpr> outside_forall = new List<BoolExpr>();
            List<Expr> bound = new List<Expr>();
            String idx = "j";

            bound.Add(Controller.Instance.Indices[idx]);

            // set equality on unprimed pre-state and primed post-state for all indexed variables of all other processes (those not making the move) (e.g., q[j]' == q[j])
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            if (!universalIndexVariableResets.Contains(v.Key))
                            {
                                //grab only idx
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));
                            }
                            else
                            {
                                if (uguardReset != null)
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (universalIndexVariableResets != null && !universalIndexVariableResets.Contains(v.Key))
                            {
                                //grab only idx
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));

                                // add basic universal guard
                                // TODO: CHECK IF THIS WORKS WITH RESETS
                                if (uguardReset != null && !uguardReset.ToString().Contains(Controller.PRIME_SUFFIX) && !uguardReset.ToString().Contains(Controller.PRIME_SUFFIX_PARSER))
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                            else
                            {
                                if (uguardReset != null)
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all unprimed pre-state and primed post-state of all indexed variables ***NOT APPEARING IN THE RESET*** for the process making the move (e.g., x[h]' == x[h], if x[h] is not reset)
            if (indexMakingMove != null)
            {
                if (indexVariableResets != null)
                {
                    foreach (var v in indexVariableResets)
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v], indexMakingMove)));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v], indexMakingMove)));
                                    break;
                                }
                        }
                    }
                }
            }

            if (globalVariableResets != null)
            {
                // set equality on all unprimed pre-state and primed post-tate of all global variables ***NOT APPEARING IN THE RESET*** (e.g., g' == g, if g is not reset)
                foreach (var v in globalVariableResets)
                {
                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v], Controller.Instance.GlobalVariablesPrimed[v]));
                }
            }
            List<BoolExpr> ibds = new List<BoolExpr>();
            if (Controller.Instance.IndexOption == Controller.IndexOptionType.naturalOneToN)
            {
                ibds.Add(Controller.Instance.Z3.MkGe((ArithExpr)Controller.Instance.Indices[idx], (ArithExpr)Controller.Instance.IndexOne));
                ibds.Add(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.Indices[idx], (ArithExpr)Controller.Instance.IndexN));
            }

            Expr ret;
            Expr fand = Controller.Instance.Z3.MkAnd(f.ToArray());
            if (indexMakingMove != null)
            {
                Expr distinct = Controller.Instance.Z3.MkDistinct(bound.First(), indexMakingMove);

                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.integer:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies((BoolExpr)distinct, (BoolExpr)fand));
                        break;
                    case Controller.IndexOptionType.naturalOneToN:
                        if (N == 0) // symbolic 
                        {
                            ibds.Add((BoolExpr)distinct);
                            ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd(ibds.ToArray()), (BoolExpr)fand));
                        }
                        else // expanded
                        {
                            List<BoolExpr> forallList = new List<BoolExpr>();
                            for (uint i = 1; i <= N; i++)
                            {
                                uint ihack = 0;
                                uint.TryParse(indexMakingMove.ToString(), out ihack);

                                if (i == ihack)
                                {
                                    continue;
                                }

                                // todo next: indexing checking
                                //BoolExpr fandCopy = (BoolExpr)this.MkImplies((BoolExpr)distinct, (BoolExpr)fand).Substitute(bound[0], this.MkInt(i));
                                BoolExpr fandCopy = (BoolExpr)fand.Substitute(bound[0], Controller.Instance.Z3.MkInt(i));
                                forallList.Add(fandCopy);
                            }
                            ret = Controller.Instance.Z3.MkAnd(forallList.ToArray());
                        }
                        break;
                    case Controller.IndexOptionType.enumeration:
                    default:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies((BoolExpr)distinct, (BoolExpr)fand));
                        break;
                }
            }
            else
            {
                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.integer:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), fand);
                        break;
                    case Controller.IndexOptionType.naturalOneToN:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd((BoolExpr[])ibds.ToArray()), (BoolExpr)fand));
                        break;
                    case Controller.IndexOptionType.enumeration:
                    default:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), fand); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                }
            }

            ret = Controller.Instance.Z3.MkTrue();
            // only add the outside forall constraints if there are any
            if (outside_forall.Count > 0)
            {
                //outside_forall.Add((BoolExpr)ret); // prettier printing (fewer ands)
                ret = Controller.Instance.Z3.MkAnd(outside_forall.ToArray());
            }
            return ret;
        }










        /**
         * Identity function for all non-continuous variables
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         * 
         * indexForall is the name of the universally quantified index
         */
        public Expr timeIdentity(Expr indexForall)
        {
            List<BoolExpr> f = new List<BoolExpr>();

            // set equality on all non-clock variables
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, indexForall), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType != Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, indexForall), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType != Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all global variables
            foreach (var v in Controller.Instance.Sys.Variables)
            {
                if (v.UpdateType != Variable.VarUpdateType.continuous)
                {
                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.GlobalVariablesPrimed[v.Name]));
                }
            }

            if (f.Count > 1)
            {
                return Controller.Instance.Z3.MkAnd(f.ToArray());
            }
            else if (f.Count == 1)
            {
                return f[0];
            }
            else
            {
                return Controller.Instance.Z3.MkTrue();
            }
        }

        /**
         * Identity function for all continuous variables
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         * 
         * indexForall is the name of the universally quantified index
         */
        public Expr timeNoFlowIdentity(Expr indexForall)
        {
            List<BoolExpr> f = new List<BoolExpr>();

            // set equality on all non-clock variables
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType == Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, indexForall), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType == Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all global variables
            foreach (var v in Controller.Instance.Sys.Variables)
            {
                if (v.UpdateType == Variable.VarUpdateType.continuous)
                {
                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.GlobalVariablesPrimed[v.Name]));
                }
            }

            if (f.Count > 1)
            {
                return Controller.Instance.Z3.MkAnd(f.ToArray());
            }
            else if (f.Count == 1)
            {
                return f[0];
            }
            else
            {
                return Controller.Instance.Z3.MkTrue();
            }
        }



        public TransitionStructure makeTimeTransition(uint N, uint k, Expr current)
        {
            AHybridAutomaton h = this._has.First();
            return new TransitionStructure(this.makeFlowsAll(h, current, N, k), this.makeFlowsAll(h, current, N, k), Transition.TimeTransition);
        }

        /**
         * Return a variable with the specified name if one exists
         */
        public Variable GetVariableByName(String name)
        {
            if (this._variables != null)
            {
                return this._variables.Find(v => v.Name == name);
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