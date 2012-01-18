﻿using System;
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
    public class Holism
    {
        /**
         * Hybrid automata
         */
        private List<ConcreteHybridAutomaton> _has;

        /**
         * Properties to be checked
         */
        protected List<Property> _properties;

        /**
         * Global variables
         */
        protected ISet<Variable> _variables = new HashSet<Variable>();

        /**
         * Gettor for global variables
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

            while (true)
            {
                Model model = null;
                Term proof = null;
                Term[] core = null;
                Property p = null;

                if (property_idx == this.Properties.Count) // && this.Properties[property_idx].Status != StatusTypes.toProcess)
                {
                    break;
                }

                if (restart)
                {
                    Controller.Instance.Z3.Push(); // PUSH1_POP1
                    Controller.Instance.Z3.CheckAndGetModel(out model);
                    Term a = Controller.Instance.Z3.GetAssignments();
                    System.Console.WriteLine("\n\r\n\rASSUMPTIONS: \n\r" + a.ToString() + "\n\r\n\r");

                    System.Console.WriteLine("\n\rProperties proved and used as assumption lemmas: \n\r\n\r");
                    foreach (var ptmp in this.Properties)
                    {
                        if (ptmp.Status == StatusTypes.inductiveInvariant)
                        {
                            System.Console.WriteLine(ptmp.Formula.ToString() + "\n\r\n\r");
                        }

                        if (ptmp.Status == StatusTypes.inductive)
                        {
                            foreach (var pt in ptmp.InductiveInvariants)
                            {
                                System.Console.WriteLine(pt.ToString() + "\n\r\n\r");
                            }
                        }
                    }

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
                    if (core != null)
                    {
                        Console.WriteLine("Unsat core:\n\r");
                        foreach (Term c in core)
                        {
                            Console.WriteLine("{0}", c);
                        }
                        core = null;
                    }
                    Controller.Instance.Z3.Pop(); // PUSH1_POP1

                    restart = false; // don't do this at every run
                    property_idx = 0; // start back over on the properties
                }

                p = this._properties[property_idx];
                property_idx++;
                if (p.Status == StatusTypes.toProcess)
                {
                    p.InductiveInvariants = new List<Term>(); // need to reset this as well
                    p.Status = StatusTypes.unknown;
                }
                else
                {
                    continue;
                }

                Controller.Instance.TimerStats.Reset();
                Controller.Instance.TimerStats.Start();

                proveCount = 0;
                subpart = false;
                iinv = true; // reset invariant shortcircuit var
                inv = true;
                Term hidx = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);
                List<Transition> tViolate = new List<Transition>(); // list of transitions which violate invariant

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
                String tmp_stat;
                if (!Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies(h.Initial, p.Formula), out model, out core, out tmp_stat, true))
                {
                    inv = false; // actually, perhaps we only check the invariant if we proved the term?
                    iinv = false;
                    p.Status = StatusTypes.disproved;
                    if (core != null)
                    {
                        Console.WriteLine("Unsat core:\n\r");
                        foreach (Term c in core)
                        {
                            Console.WriteLine("{0}", c);
                        }
                        core = null;
                    }
                }

                //if (iinv)
                if (true)
                {
                    List<Term> timeall = new List<Term>(); // conjunction of all possible locations for time transition

                    foreach (ConcreteLocation l in h.Locations)
                    {
                        foreach (var t in l.Transitions)
                        {
                            Term inductiveInvariant = p.Formula;
                            Term inductiveInvariantPrimed = p.Formula;
                            Controller.Instance.Z3.primeAllVariables(ref inductiveInvariantPrimed);

                            List<Term> locInvariant = new List<Term>();
                            locInvariant.Add(l.StatePredicate); // discrete location prestate   (e.g., loc[i]  = 1)
                            locInvariant.Add(t.ToTerm());       // discrete location post-state (e.g., loc'[i] = 2)

                            // add guard, if one exists
                            if (t.Guard != null)
                            {
                                locInvariant.Add(t.Guard);
                            }

                            // add invariant, if one exists
                            if (l.Invariant != null)
                            {
                                locInvariant.Add(l.Invariant);
                            }

                            // add stopping condition, if one exists
                            if (l.Stop != null)
                            {
                                locInvariant.Add(l.Stop);
                            }

                            List<String> globalVariableResets = new List<String>(); // global variables not reset
                            List<String> indexVariableResets = new List<String>();  // indexed variables of process moving that are not reset

                            if (t.Reset != null)
                            {
                                locInvariant.Add(t.Reset);

                                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(t.Reset);
                                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(t.Reset);
                            }
                            else
                            {
                                // global variable was not mentioned since reset is null: add it to the identity global variables (g' = g)
                                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(null);
                                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(null);
                            }

                            // create conjunction of pre-state and post-state conditions
                            Term locInvariantAnd = Controller.Instance.Z3.MkAnd(locInvariant.ToArray());

                            List<Term> bound = new List<Term>();
                            hidx = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);
                            bound.Add(hidx);
                            Controller.Instance.Z3.replaceTerm(ref locInvariantAnd, locInvariantAnd, Controller.Instance.Indices["i"], hidx, true); // replace i by h

                            // add quantifiers based on pre-state and post-state, using implies vs. and options and indexing options
                            switch (Controller.Instance.IndexOption)
                            {
                                case Controller.IndexOptionType.naturalOneToN:
                                    switch (Controller.Instance.ExistsOption)
                                    {
                                        case Controller.ExistsOptionType.and:
                                            locInvariantAnd = Controller.Instance.Z3.MkAnd(hidx >= Controller.Instance.IntOne & hidx <= Controller.Instance.IndexN, locInvariantAnd & Controller.Instance.Z3.forallIdentity(hidx, globalVariableResets, indexVariableResets)); // 1 <= h <= N, enforce identity for all other processes not moving
                                            break;
                                        case Controller.ExistsOptionType.implies:
                                        default:
                                            locInvariantAnd = Controller.Instance.Z3.MkImplies(hidx >= Controller.Instance.IntOne & hidx <= Controller.Instance.IndexN, locInvariantAnd & Controller.Instance.Z3.forallIdentity(hidx, globalVariableResets, indexVariableResets)); // 1 <= h <= N, enforce identity for all other processes not moving
                                            break;
                                    }
                                    break;
                                case Controller.IndexOptionType.enumeration:
                                case Controller.IndexOptionType.integer:
                                default:
                                    locInvariantAnd = locInvariantAnd & Controller.Instance.Z3.forallIdentity(hidx, globalVariableResets, indexVariableResets);
                                    break;
                            }

                            //Pattern pA = Controller.Instance.Z3.MkPattern(new Term[] { hidx >= Controller.Instance.IntOne, hidx <= Controller.Instance.N });
                            //Pattern[] pS = new Pattern[] { pA };

                            inductiveInvariant = inductiveInvariant & Controller.Instance.Z3.MkExists(0, bound.ToArray(), null, locInvariantAnd);

                            // alternative next, get the body and recreate
                            //Quantifier orig = inductiveInvariant.GetQuantifier();
                            //inductiveInvariant = inductiveInvariant.GetQuantifier().Body & Controller.Instance.Z3.MkExists(0, bound.ToArray(), null, locInvariantAnd);
                            //inductiveInvariant = Controller.Instance.Z3.MkForall(orig.Weight, null, orig.Sorts, orig.Names, inductiveInvariant);

                            //if (!Controller.Instance.Z3.checkTerm(inductiveInvariant, out model, out core, true)) // if the guard is unsatisfiable, exclude this from being an inductive invariant... todo: check
                            //{
                            //    ////shouldn't have to do this
                            //    iinv = iinv & false;
                            //    tViolate.Add(t);
                            //    p.Counterexamples.Add(new Counterexample(model, inductiveInvariant));
                            //}

                            //if (Controller.Instance.Z3.checkTerm(inductiveInvariant, out model, out core, true))
                            //if (Controller.Instance.Z3.proveTerm(inductiveInvariant, out model, out core, true))
                            if (true)
                            {
                                Controller.Instance.Z3.checkTerm(inductiveInvariant, out model, out core, true);
                                Console.WriteLine("\n\r<><><><><> GUARDED MODEL START\n\r\n\r");
                                Console.WriteLine(inductiveInvariant.ToString() + "\n\r\n\r");
                                if (model != null)
                                {
                                    model.Display(Console.Out);
                                    model = null;
                                }
                                Console.WriteLine("\n\r<><><><><> GUARDED MODEL END\n\r\n\r");

                                Term claim = Controller.Instance.Z3.MkImplies(inductiveInvariant, inductiveInvariantPrimed);
                                Controller.Instance.Z3.checkTerm(claim, out model, out core, true);

                                Console.WriteLine("\n\r<><><><><> INDUCTIVE INVARIANT START\n\r\n\r");
                                Console.WriteLine(claim.ToString() + "\n\r\n\r");
                                if (model != null)
                                {
                                    model.Display(Console.Out);
                                }
                                Console.WriteLine("\n\r<><><><><> INDUCTIVE INVARIANT END\n\r\n\r");

                                //Controller.Instance.Z3.Push();
                                //Controller.Instance.Z3.AssertCnstr(inductiveInvariant);
                                //Controller.Instance.Z3.AssertCnstr(inductiveInvariantPrimed);
                                //claim = Controller.Instance.Z3.Simplify(claim);

                                //if (Controller.Instance.Z3.proveTerm(inductiveInvariantPrimed, out model, out core, true))
                                if (Controller.Instance.Z3.proveTerm(claim, out model, out core, out tmp_stat, true))
                                {
                                    p.Statistics.Add(tmp_stat);
                                    if (core != null)
                                    {
                                        Console.WriteLine("Unsat core:\n\r");
                                        foreach (Term c in core)
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
                                    p.Counterexamples.Add(new Counterexample(model, claim));
                                }
                                //Controller.Instance.Z3.Pop();

                                p.addInductiveInvariant(claim);
                            }
                        } // end discrete actions

                        hidx = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);

                        if (l.Flow == null)
                        {
                            Term tmpterm = Controller.Instance.Z3.MkImplies(l.StatePredicate, Controller.Instance.Z3.timeNoFlowIdentity(hidx));
                            Controller.Instance.Z3.replaceTerm(ref tmpterm, tmpterm, Controller.Instance.Indices["i"], hidx, true); // replace i by h

                            timeall.Add(tmpterm);

                            if (timeall.Count != h.Locations.Count) // only continue if nothing in timed list, otherwise if the last location has null flow, the others will also get skipped
                            {
                                continue; // no dynamics (e.g., x' == 0), skip time transition
                            }
                        }

                        Term timeii = p.Formula;
                        Term timeiiPrimed = p.Formula;
                        Controller.Instance.Z3.primeAllVariables(ref timeiiPrimed);

                        List<Term> exprlist = new List<Term>();
                        Term expr = null;
                        Term t1 = Controller.Instance.Z3.MkConst("t_1", Controller.Instance.RealType);
                        Term t2 = Controller.Instance.Z3.MkConst("t_2", Controller.Instance.RealType);

                        if (l.Invariant != null)
                        {
                            Term tmpterm = l.Invariant;

                            foreach (var v in h.Variables)
                            {
                                if (v.UpdateType == Variable.VarUpdateType.continuous)
                                {
                                    switch (Controller.Instance.DataOption)
                                    {
                                        case Controller.DataOptionType.array:
                                            {
                                                Controller.Instance.Z3.replaceTerm(ref tmpterm, tmpterm, Controller.Instance.DataA.IndexedVariableDecl[v.Name], Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], false);
                                                break;
                                            }
                                        case Controller.DataOptionType.uninterpreted_function:
                                        default:
                                            {
                                                Controller.Instance.Z3.replaceFuncDecl(ref tmpterm, tmpterm, Controller.Instance.DataU.IndexedVariableDecl[v.Name], Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], false);
                                                break;
                                            }
                                    }
                                }
                            }
                            exprlist.Add(tmpterm);
                        }
                        if (l.Stop != null)
                        {
                            Term tmpterm = Controller.Instance.Z3.MkImplies(l.Stop, Controller.Instance.Z3.MkEq(t1, t2));

                            foreach (var v in h.Variables)
                            {
                                if (v.UpdateType == Variable.VarUpdateType.continuous)
                                {
                                    switch (Controller.Instance.DataOption)
                                    {
                                        case Controller.DataOptionType.array:
                                            {
                                                Controller.Instance.Z3.replaceTerm(ref tmpterm, tmpterm, Controller.Instance.DataA.IndexedVariableDecl[v.Name], Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Name], false);
                                                break;
                                            }
                                        case Controller.DataOptionType.uninterpreted_function:
                                        default:
                                            {
                                                Controller.Instance.Z3.replaceFuncDecl(ref tmpterm, tmpterm, Controller.Instance.DataU.IndexedVariableDecl[v.Name], Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Name], false);
                                                break;
                                            }
                                    }
                                }
                            }
                            exprlist.Add(tmpterm);
                        }

                        // do flow afterward, it already has primed variables
                        if (l.Flow != null)
                        {
                            exprlist.Add(l.Flow);
                        }
                        // mkimplies: l.StatePredicate
                        //l.StatePredicate;
                        List<Term> bt = new List<Term>();
                        hidx = Controller.Instance.Z3.MkConst("h", Controller.Instance.IndexType);
                        bt.Add(hidx);

                        if (Controller.Instance.TimeOption == Controller.TimeOptionType.separated)
                        {
                            exprlist.Add(l.StatePredicate); // control location, e.g., q[h] == 2
                        }

                        expr = Controller.Instance.Z3.MkAnd(exprlist.ToArray());

                        if (Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction)
                        {
                            expr = Controller.Instance.Z3.MkImplies(l.StatePredicate, expr); // control location, e.g., q[h] == 2 implies (inv, guard, flow, etc.)
                        }

                        Controller.Instance.Z3.replaceTerm(ref expr, expr, Controller.Instance.Indices["i"], hidx, true); // replace i by h

                        // if we haven't yet add every location's invariant, keep adding them on
                        if (Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction && timeall.Count < h.Locations.Count)
                        {
                            timeall.Add(expr);

                            if (timeall.Count != h.Locations.Count)
                            {
                                continue;
                            }
                        }

                        expr = Controller.Instance.Z3.MkAnd(timeall.ToArray());


                        switch (Controller.Instance.IndexOption)
                        {
                            case Controller.IndexOptionType.naturalOneToN:
                                {
                                    switch (Controller.Instance.ExistsOption)
                                    {
                                        case Controller.ExistsOptionType.and:
                                            expr = Controller.Instance.Z3.MkForall(0, bt.ToArray(), null, Controller.Instance.Z3.MkImplies(hidx >= Controller.Instance.IndexOne & hidx <= Controller.Instance.IndexN, expr & Controller.Instance.Z3.timeIdentity(hidx)));
                                            break;
                                        case Controller.ExistsOptionType.implies:
                                        default:
                                            expr = Controller.Instance.Z3.MkForall(0, bt.ToArray(), null, Controller.Instance.Z3.MkImplies(hidx >= Controller.Instance.IndexOne & hidx <= Controller.Instance.IndexN, expr & Controller.Instance.Z3.timeIdentity(hidx)));
                                            break;
                                    }
                                    break;
                                }
                            case Controller.IndexOptionType.integer:
                            case Controller.IndexOptionType.enumeration:
                            default:
                                expr = Controller.Instance.Z3.MkForall(0, bt.ToArray(), null, expr & Controller.Instance.Z3.timeIdentity(hidx));
                                break;
                        }

                        // if we have a stop condition, or if we're doing the conjunction (assume at least one location has a stop)
                        if (l.Stop != null || Controller.Instance.TimeOption == Controller.TimeOptionType.conjunction)
                        {
                            expr = Controller.Instance.Z3.MkForall(0, new Term[] { t2 }, null, Controller.Instance.Z3.MkAnd(t2 >= Controller.Instance.RealZero & t2 <= t1, expr)); // todo: seems correct with this as and instead of implies, doulbe check
                        }

                        switch (Controller.Instance.ExistsOption)
                        {
                            case Controller.ExistsOptionType.and:
                                expr = Controller.Instance.Z3.MkExists(0, new Term[] { t1 }, null, Controller.Instance.Z3.MkAnd(t1 >= Controller.Instance.RealZero, expr)); // broken with invariants if using implies
                                break;
                            case Controller.ExistsOptionType.implies:
                            default:
                                expr = Controller.Instance.Z3.MkExists(0, new Term[] { t1 }, null, Controller.Instance.Z3.MkImplies(t1 >= Controller.Instance.RealZero, expr));
                                break;
                        }

                        timeii = timeii & expr;
                        p.addInductiveInvariant(timeii);

                        //if (Controller.Instance.Z3.checkTerm(timeii, out model, out core, true))
                        //if (Controller.Instance.Z3.proveTerm(inductiveInvariant, out model, out core, true))
                        if (true)
                        {
                            timeii = Controller.Instance.Z3.MkImplies(timeii, timeiiPrimed);

                            if (Controller.Instance.Z3.proveTerm(timeii, out model, out core, out tmp_stat, true))
                            {
                                p.Statistics.Add(tmp_stat);
                                // proved inductive invariant (for this location of the timed transition)
                                if (core != null)
                                {
                                    Console.WriteLine("Unsat core:\n\r");
                                    foreach (Term c in core)
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
                                p.Counterexamples.Add(new Counterexample(model, timeii));
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
                    Console.WriteLine("\n\r\n\rProperty was NOT an inductive invariant! Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    Console.WriteLine("\n\r\n\rProperty was an inductive invariant! Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.inductiveInvariant;

                    // assert the property as a lemma
                    Controller.Instance.Z3.AssertCnstr(p.Formula);

                    Term formulaPrime = p.Formula;
                    Controller.Instance.Z3.primeAllVariables(ref formulaPrime);
                    Term simple_ii = Controller.Instance.Z3.MkImplies(p.Formula, formulaPrime);
                    Controller.Instance.Z3.AssertCnstr(simple_ii);

                    //Controller.Instance.Z3.AssertCnstr(Controller.Instance.Z3.MkOr(p.InductiveInvariants.ToArray())); // disjunction of all transitions is the transition relation, not conjunction!
                    // also assert the inductive invariant claim since it is strictly stronger than an invariant property (i.e., ii => i, but ii !<= i necessarily)
                }


                // property is not inductive (a property may be inductive without being an inductive invariant, e.g., if only the initial condition check fails)
                if (!inv)
                {
                    Console.WriteLine("\n\r\n\rProperty was NOT inductive! Property checked was: \n\r" + p.Formula.ToString());
                    p.Status = StatusTypes.disproved;
                }
                else
                {
                    // only do this for non-invariants
                    if (!iinv)
                    {
                        Console.WriteLine("\n\r\n\rProperty was inductive! Property checked was: \n\r" + p.Formula.ToString());
                        p.Status = StatusTypes.inductive;

                        //Controller.Instance.Z3.AssertCnstr(p.Formula); // probably don't want to assert this, as this would require it to be invariant

                        p.InductiveFormula = Controller.Instance.Z3.MkOr(p.InductiveInvariants.ToArray());
                    }
                }
                Controller.Instance.TimerStats.Stop();

                // once we assert a property as a lemma, we go back to all other formulas and attempt to reprove them so that the order of the lemma assertions does not matter
                if (subpart || iinv || inv)
                {
                    restart = true;

                    foreach (var ptmp in this.Properties)
                    {
                        if (ptmp.Status == StatusTypes.disproved)
                        {
                            ptmp.Status = StatusTypes.toProcess;
                            ptmp.InductiveInvariants = new List<Term>(); // need to reset this as well
                            ptmp.Counterexamples = new List<Counterexample>();

                        }
                    }

                    property_idx = 0; // edge case if last lemma is disproved
                }

                p.Time = Controller.Instance.TimerStats.Elapsed;
            }


            System.Console.WriteLine("\n\r\n\rDISPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine("PROPERTY DISPROVED =====================================================================\n\r");
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r\n\r");

                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r");

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
                            System.Console.WriteLine("Negation of inductive invariant claim:\n\r\n\r");
                            System.Console.WriteLine((!ce.Claim).ToString() + "\n\r\n\r");
                            System.Console.WriteLine("Simplified negation of inductive invariant claim:\n\r\n\r");
                            System.Console.WriteLine(Controller.Instance.Z3.Simplify(!ce.Claim).ToString() + "\n\r\n\r");
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

            System.Console.WriteLine("DISPROVED INVARIANTS SUMMARY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r\n\r");
                    System.Console.WriteLine("Statistics: \n\r");
                    foreach (var stmp in p.Statistics)
                    {
                        System.Console.WriteLine(stmp + "\n\r\n\r");
                    }
                }
            }

            System.Console.WriteLine("\n\rPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.inductiveInvariant)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r\n\r");
                    System.Console.WriteLine("Statistics: \n\r");
                    foreach (var stmp in p.Statistics)
                    {
                        System.Console.WriteLine(stmp + "\n\r\n\r");
                    }
                }
            }

            System.Console.WriteLine("\n\rPROVED INDUCTIVE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.inductive)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r\n\r");
                    System.Console.WriteLine("Statistics: \n\r");
                    foreach (var stmp in p.Statistics)
                    {
                        System.Console.WriteLine(stmp + "\n\r\n\r");
                    }
                }
            }




            System.Console.WriteLine("DISPROVED INVARIANTS SUMMARY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.disproved)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r\n\r");
                }
            }

            System.Console.WriteLine("\n\rPROVED INVARIANTS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.inductiveInvariant)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r\n\r");
                }
            }

            System.Console.WriteLine("\n\rPROVED INDUCTIVE >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\r");
            foreach (Property p in this.Properties)
            {
                if (p.Status == StatusTypes.inductive)
                {
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r");
                    System.Console.WriteLine("Time: " + String.Format("{0}", p.Time.TotalSeconds) + "\n\r\n\r");
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