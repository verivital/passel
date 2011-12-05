using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;
using phyea.controller.smt;

namespace phyea.model
{
    /**
     * Complete system specification (couldn't name it system for obvious reasons, e.g., name conflicts)
     * Contains property specifications, global variables, and indexed hybrid automata
     */
    public abstract class AHolism
    {
        /**
         * Hybrid automata
         */
        private List<AConcreteHybridAutomaton> _has;

        /**
         * Properties to be checked
         */
        protected List<Property> _properties;

        /**
         * Global variables
         */
        protected ISet<AVariable> _variables = new HashSet<AVariable>();

        /**
         * Gettor for global variables
         */
        public ISet<AVariable> Variables
        {
            get
            {
                if (this._variables == null)
                {
                    this._variables = new HashSet<AVariable>();
                }
                return this._variables;
            }
            set { this._variables = value; }
        }

        /**
         * Default Constructor
         */
        public AHolism()
        {
            this._properties = new List<Property>();
            this._has = new List<AConcreteHybridAutomaton>();
        }

        /**
         * Accessor for hybrid automata
         */
        public List<AConcreteHybridAutomaton> HybridAutomata
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
         * Add a hybrid automaton to the list of automata
         */
        public void addHybridAutomaton(AConcreteHybridAutomaton ha)
        {
            if (this._has == null)
            {
                this._has = new List<AConcreteHybridAutomaton>();
            }
            this._has.Add(ha);
        }

        /**
         * Assume each property is a candidate inductive invariant, then we need to check each transition with respect to it
         */
        public void checkInductiveInvariants()
        {
            AConcreteHybridAutomaton h = this._has.First(); // assume only one ha
            bool iinv = true;

            Model m;
            Controller.Instance.Z3.Push();
            Controller.Instance.Z3.CheckAndGetModel(out m);
            Term a = Controller.Instance.Z3.GetAssignments();
            System.Console.WriteLine("Assumptions: \n\r" + a.ToString() + "\n\r\n\r");

            Model model = null;
            Term proof = null;
            Term[] core;
            //switch (this.CheckAndGetModel(out model))
            LBool ca = Controller.Instance.Z3.CheckAssumptions(out model, null, out proof, out core);
            if (ca == LBool.False || ca == LBool.Undef)
            {
                throw new Exception("ERROR: basic assumptions on data types, indices, etc. are not satisfied!");
            }
            if (model != null)
            {
                System.Console.WriteLine("Model for basic assumptions: \n\r\n\r");
                model.Display(Console.Out);
                model.Dispose(); // todo: smarter way to do this?
            }
            Controller.Instance.Z3.Pop();

            foreach (var p in this._properties)
            {
                iinv = true; // reset invariant shortcircuit var
                List<ATransition> tViolate = new List<ATransition>(); // list of transitions which violate invariant

                /*
                Boolean tst = Controller.Instance.Z3.checkTerm(p.Formula, out model);
                tst = Controller.Instance.Z3.checkTerm(h.Initial, out model);
                tst = Controller.Instance.Z3.checkTerm(p.Formula & h.Initial, out model);
                tst = Controller.Instance.Z3.checkTerm(p.Formula | h.Initial, out model);
                tst = Controller.Instance.Z3.checkTerm(Controller.Instance.Z3.MkImplies(p.Formula, h.Initial), out model);
                tst = Controller.Instance.Z3.checkTerm(Controller.Instance.Z3.MkImplies(h.Initial, p.Formula), out model);
                tst = Controller.Instance.Z3.checkTerm(Controller.Instance.Z3.MkIff(p.Formula, h.Initial), out model);

                tst = Controller.Instance.Z3.proveTerm(p.Formula, out model);
                tst = Controller.Instance.Z3.proveTerm(h.Initial, out model);
                tst = Controller.Instance.Z3.proveTerm(p.Formula & h.Initial, out model);
                tst = Controller.Instance.Z3.proveTerm(p.Formula | h.Initial, out model);
                tst = Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies(p.Formula, h.Initial), out model);
                tst = Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies(h.Initial, p.Formula), out model);
                tst = Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkIff(p.Formula, h.Initial), out model);
                */

                //Controller.Instance.Z3.Push();
                //Controller.Instance.Z3.AssertCnstr(p.Formula);

                //Term initialImpliesInv = !Controller.Instance.Z3.MkAnd(h.Initial, p.Formula); // todo: check this
                //Term initialImpliesInv = Controller.Instance.Z3.MkImplies(p.Formula, h.Initial); // todo: check this
                //if (Controller.Instance.Z3.proveTerm(initialImpliesInv))

                if (!Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies(h.Initial, p.Formula), out model))
                {
                    iinv = false; // actually, perhaps we only check the invariant if we proved the term?
                }

                //Controller.Instance.Z3.Pop(1);

                foreach (AConcreteLocation l in h.Locations)
                {
                    foreach (var t in l.Transitions)
                    {
                        Term inductiveInvariant = p.Formula;
                        Term inductiveInvariantPrimed = p.Formula;
                        Controller.Instance.Z3.primeAllVariables(ref inductiveInvariantPrimed);

                        Term locInvariant = l.StatePredicate & t.ToTerm(); // discrete location prestate and post-state (e.g., loc[i] = 1 and loc'[i] = 2)

                        if (l.Invariant != null)
                        {
                            locInvariant = locInvariant & l.Invariant;
                        }

                        if (l.Stop != null)
                        {
                            locInvariant = locInvariant & l.Stop;
                        }

                        // todo: pull in transition precondition and effect: set iinv false if not invariant
                        List<Term> bound = new List<Term>();
                        //bound.Add(Controller.Instance.Indices["i"]);
                        Term hidx = Controller.Instance.Z3.MkConst("h", Controller.Instance.IntType);
                        bound.Add(hidx);

                        //locInvariant = Controller.Instance.Z3.MkImplies(bound.First() >= Controller.Instance.IntOne & bound.First() <= Controller.Instance.N, locInvariant); // 1 <= h <= N
                        locInvariant = Controller.Instance.Z3.MkAnd(bound.First() >= Controller.Instance.IntOne & bound.First() <= Controller.Instance.N, locInvariant); // 1 <= h <= N

                        List<String> globalVariableResets = new List<String>();
                        List<String> indexVariableResets = new List<String>();

                        if (t.Reset != null)
                        {
                            locInvariant = locInvariant & t.Reset;

                            globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(t.Reset);
                            indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(t.Reset);
                        }
                        else
                        {
                            // global variable was not mentioned since reset is null: add it to the identity global variables (g' = g)
                            globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(null);
                            indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(null);
                        }

                        if (t.Guard != null)
                        {
                            locInvariant = locInvariant & t.Guard;
                        }

                        Controller.Instance.Z3.replaceTerm(ref locInvariant, locInvariant, Controller.Instance.Indices["i"], hidx, true); // replace i by h

                        System.Console.WriteLine("Checking if location invariant, stopping condition, and transition pre-condition are satisfiable (i.e., transition could be taken):\n\r\n\r");
                        Controller.Instance.Z3.checkTerm(locInvariant, out model, true);

                        System.Console.WriteLine("\n\r\n\rChecking (1) if forcing all other processes not to change breaks anything, and (2) if location invariant, stopping condition, and transition pre-condition are satisfiable (i.e., transition could be take):\n\r\n\r");
                        Controller.Instance.Z3.checkTerm(Controller.Instance.Z3.MkExists(0, bound.ToArray(), null, locInvariant & Controller.Instance.Z3.forallIdentity(hidx, globalVariableResets, indexVariableResets)), out model, true);

                        inductiveInvariant = inductiveInvariant & Controller.Instance.Z3.MkExists(0, bound.ToArray(), null, locInvariant & Controller.Instance.Z3.forallIdentity(hidx, globalVariableResets, indexVariableResets));
                        System.Console.WriteLine("Checking if inductive invariant in pre-state is satisfiable (IT SHOULD BE):\n\r\n\r");
                        if (!Controller.Instance.Z3.checkTerm(inductiveInvariant, out model, true)) // if the guard is unsatisfiable, exclude this from being an inductive invariant... todo: check
                        {
                            // shouldn't have to do this
                            iinv = iinv & false;
                            tViolate.Add(t);
                            p.Counterexamples.Add(new Counterexample(model, inductiveInvariant));
                        }

                        if (Controller.Instance.Z3.proveTerm(inductiveInvariant, out model, true)) // i.e., make sure the guard condition is satisfied before we try to prove the whole term, otherwise it doesn't make sense to try to prove the invariant is inductive (because it obviously is)
                        {
                            Console.WriteLine("\n\r<><><><><> GUARDED MODEL START\n\r\n\r");
                            Console.WriteLine(inductiveInvariant.ToString() + "\n\r\n\r");
                            model.Display(Console.Out);
                            Console.WriteLine("\n\r<><><><><> GUARDED MODEL END\n\r\n\r");

                            Term claim = Controller.Instance.Z3.MkImplies(inductiveInvariant, inductiveInvariantPrimed);
                            //claim = Controller.Instance.Z3.Simplify(claim);

                            if (Controller.Instance.Z3.proveTerm(claim, out model, true))
                            {
                                // proved inductive invariant (for this transition)
                            }
                            else
                            {
                                iinv = iinv & false;
                                tViolate.Add(t);
                                p.Counterexamples.Add(new Counterexample(model, claim));
                            }
                        }
                    } // end discrete actions

                    if (l.Flow != null && Controller.Instance.Z3.findTerm(l.Flow, Controller.Instance.RealZero, true)) // todo: generalize, probably need expression evaluation at this point to simplify parsing
                    {
                        continue; // no dynamics (e.g., x' == 0), skip time transition
                    }

                    Term timeii = p.Formula;
                    Term timeiiPrimed = p.Formula;
                    Controller.Instance.Z3.primeAllVariables(ref timeiiPrimed);

                    //todo: check the timed transition: set iinv false if not invariant
                    Term expr = null;
                    Term delta = Controller.Instance.Z3.MkConst("delta", Controller.Instance.RealType);
                    Term deltaPrime = Controller.Instance.Z3.MkConst("delta'", Controller.Instance.RealType);

                    if (l.Invariant != null)
                    {
                        expr = l.Invariant;
                    }
                    if (l.Stop != null)
                    {
                        /*
                        Term tmpterm = Controller.Instance.Z3.MkImplies(l.Stop, Controller.Instance.Z3.MkEq(delta, deltaPrime));
                        if (expr != null)
                        {
                            expr = expr & tmpterm;
                        }
                        else
                        {
                            expr = tmpterm;
                        }
                         * */
                    }

                    // prime continuous variables in stopping condition and invariant
                    if (expr != null)
                    {
                        foreach (var v in h.Variables)
                        {
                            if (v.UpdateType == AVariable.VarUpdateType.continuous)
                            {
                                Controller.Instance.Z3.replaceFuncDecl(ref expr, expr, Controller.Instance.IndexedVariableDecl[v.Name], Controller.Instance.IndexedVariableDeclPrimed[v.Name], false);
                            }
                        }
                    }

                    // do flow afterward, it already has primed variables
                    if (l.Flow != null)
                    {
                        if (expr != null)
                        {
                            expr = expr & l.Flow;
                        }
                        else
                        {
                            expr = l.Flow;
                        }
                    }

                    List<Term> bt = new List<Term>();
                    Term ht = Controller.Instance.Z3.MkConst("h", Controller.Instance.IntType);
                    bt.Add(ht);
                    Controller.Instance.Z3.replaceTerm(ref expr, expr, Controller.Instance.Indices["i"], ht, true); // replace i by h


                    expr = Controller.Instance.Z3.MkForall(0, bt.ToArray(), null, Controller.Instance.Z3.MkImplies(ht >= Controller.Instance.IntOne & ht <= Controller.Instance.N, expr & Controller.Instance.Z3.timeIdentity(ht)));
                    if (l.Stop != null)
                    {
                        //expr = Controller.Instance.Z3.MkForall(0, new Term[] { deltaPrime }, null, Controller.Instance.Z3.MkImplies((deltaPrime >= Controller.Instance.RealZero & deltaPrime <= delta), expr));
                    }
                    expr = Controller.Instance.Z3.MkExists(0, new Term[] { delta }, null, delta >= Controller.Instance.RealZero & expr);

                    timeii = timeii & expr;
                    timeii = Controller.Instance.Z3.MkImplies(timeii, timeiiPrimed);

                    if (Controller.Instance.Z3.proveTerm(timeii, out model, true))
                    {
                        // proved inductive invariant (for this transition)
                    }
                    else
                    {
                        iinv = iinv & false;
                        p.TimedInductiveInvariant = timeii;
                    }
                }

                // property is not an inductive invariant
                if (!iinv)
                {
                    Console.WriteLine("\n\r\n\rProperty was NOT an inductive invariant! Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    Console.WriteLine("\n\r\n\rProperty was an inductive invariant! Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.proved;

                    // assert the property as a lemma
                    //Controller.Instance.Z3.AssertCnstr(p.Formula); // todo: re-enable once debugging done
                }
            }


            System.Console.WriteLine("\n\r\n\rDISPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine("PROPERTY DISPROVED =====================================================================\n\r");
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r\n\r");
                    if (p.TimedInductiveInvariant != null)
                    {
                        System.Console.WriteLine("Inductive invariant claim (timed):\n\r\n\r");
                        System.Console.WriteLine(p.TimedInductiveInvariant.ToString() + "\n\r\n\r");
                        System.Console.WriteLine("Simplified nductive invariant claim (timed):\n\r\n\r");
                        System.Console.WriteLine(Controller.Instance.Z3.Simplify(p.TimedInductiveInvariant).ToString() + "\n\r\n\r");
                    }
                    System.Console.WriteLine("REASONS (counterexample / trace):\n\r");
                    foreach (Counterexample ce in p.Counterexamples)
                    {
                        if (ce.Model != null)
                        {
                            System.Console.WriteLine("Counterexample model:\n\r");
                            ce.Model.Display(Console.Out);
                            ce.Model.Dispose(); // todo: smarter way to do this?
                            System.Console.WriteLine("\n\r\n\r");
                        }

                        if (ce.Claim != null)
                        {
                            System.Console.WriteLine("Inductive invariant claim:\n\r\n\r");
                            System.Console.WriteLine(ce.Claim.ToString() + "\n\r\n\r");
                            System.Console.WriteLine("Simplified inductive invariant claim:\n\r\n\r");
                            System.Console.WriteLine(Controller.Instance.Z3.Simplify(ce.Claim).ToString() + "\n\r\n\r");
                        }

                        if (ce.Transition != null)
                        {
                            System.Console.WriteLine("Counterexample transition:\n\r");
                            //System.Console.WriteLine( ce.Transition.t
                            System.Console.WriteLine("\n\r\n\r");
                        }
                    }
                    System.Console.WriteLine("END PROPERTY DISPROVED =====================================================================\n\r\n\r\n\r\n\r");
                }
            }

            System.Console.WriteLine("DISPROVED INVARIANTS SUMMARY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r\n\r");
                }
            }

            System.Console.WriteLine("\n\rPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.proved)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r\n\r");
                }
            }
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
// 1) finish continuous variable generalizations. if rate == 0, do not check time transitions in that location (e.g., in sats we do this)
// 2) add support for rectangular inclusions?
// 3) pretty printer for latex output