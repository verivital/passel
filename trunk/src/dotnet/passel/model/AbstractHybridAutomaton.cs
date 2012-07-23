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
    public class AbstractHybridAutomaton : AHybridAutomaton
    {
        /**
         * States of the abstracted hybrid automaton
         */
        protected ISet<AbstractState> _states = new HashSet<AbstractState>();

        /**
         * Valuations of the abstracted hybrid automaton
         */
        protected ISet<AbstractState> _valuations = new HashSet<AbstractState>();

        /**
         * Default constructor
         */
        public AbstractHybridAutomaton(Holism parent)
            : base(parent)
        {
        }

        public ISet<AbstractState> States
        {
            get { return this._states; }
            set { this._states = value; }
        }

        public ISet<AbstractState> Valuations
        {
            get { return this._valuations; }
            set { this._valuations = value; }
        }


        /**
         * Reference to the concrete hybrid automaton for which this is an abstraction
         */
        private ConcreteHybridAutomaton _cha;

        private ISet<Expr> _predicates;

        public ISet<Expr> Predicates
        {
            get { return this._predicates; }
            set { this._predicates = value; }
        }

        public int _S = 0;
        public int _r = 0;
        public int _T = 0;

        /**
         * Properties (abstracted from the concrete ones) to be checked in this automaton
         */
        public List<Property> Properties;

        /**
         * Given a concrete hybrid automaton, compute the abstraction
         */
        public AbstractHybridAutomaton(Holism parent, ConcreteHybridAutomaton cha)
            : base(parent)
        {
            this._cha = cha;

            this.makePredicates();                  // generate predicates to be used to generate the abstract state space
            this.makeAbstractStateSpace();          // build abstract state space
            this.makeAbstractProperties(this.Parent.Properties);    // abstract the given properties
            this.makeAbstractStateValuations();     // build explicit state space (e.g., for PHAVer output)
            this.makeAbstractInitial();             // find the initial abstract states
            //this.makeAbstractTransitions();         // build explicit transitions (e.g., for PHAVer output)

            // model check each property
            foreach (var p in this.Properties)
            {
                switch (p.Type)
                {
                    case Property.PropertyType.invariant: // safety, bad, unreachable, etc. all equivalent at this point (negated appropriately already)
                    case Property.PropertyType.bad:
                    case Property.PropertyType.safety:
                    case Property.PropertyType.unreachable:
                        this.modelCheckInvariant(this.Initial, p.Formula);
                        break;
                    default:
                        break;
                }
            }
        }

        /**
         * Abstract a given set of properties
         */
        public void makeAbstractProperties(List<Property> properties)
        {
            this.Properties = new List<Property>();

            // abstract each property
            foreach (var p in properties)
            {
                // todo: actually abstract it
                this.Properties.Add(p);
            }
        }

        public void makeAbstractInitial()
        {
            // find initial states
            // process: for the conretization of each abstract state ainv(phi), determine if initial => ainv(phi) is proved, so that initial is a subset of ainv(phi)
            List<Expr> initialConcrete = new List<Expr>();
            foreach (AbstractState qa in this._valuations)
            {
                foreach (EnvironmentState ea in qa.EnvironmentStates)
                {
                    Expr[] core;
                    Model m = null;
                    String nstr;
                    if (Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies(this._cha.Initial, ea.EnvironmentPredicate), out m, out core, out nstr))
                    {
                        qa.Initial = true;
                        initialConcrete.Add(qa.Concretization());
                    }
                }
            }

            if (initialConcrete.Count == 0)
            {
                throw new Exception("Error: could not locate any initial abstract states for which their concretization contained the concrete initial states (i.e., couldn't locate the abstract initial set of states).");
                // todo: add an option to manually specify this somehow?
            }
            else
            {
                this.Initial = Controller.Instance.Z3.MkOr((BoolExpr[])initialConcrete.ToArray());
            }
        }

        /**
         * Determine if the set of states described by the formula bad can be reached from the set of states described by initial
         */
        public Boolean modelCheckInvariant(Expr initial, Expr bad)
        {
            //Term reached = Controller.Instance.Z3.MkFalse(); // none of the state space
            Expr reached = initial;
            UInt32 iteration = 0;
            Boolean debug = true;
            TreeReach reachset = new TreeReach(initial, null);
            TreeReach reachset_root = reachset; // reference to root of the tree
            HashSet<TreeReach> toProcess = new HashSet<TreeReach>();
            Expr[] core;
            toProcess.Add(reachset);

            while (toProcess.Count > 0)
            {
                // safety check (see if intersection of bad and newly reached is non-empty by checking satisfiability of their conjunction)
                Console.WriteLine("Safety check for iteration " + iteration.ToString());
                Model m = null;
                if (Controller.Instance.Z3.checkTerm(Controller.Instance.Z3.MkAnd(reached, bad), out m, out core, debug))
                {
                    return false;
                }
                Console.WriteLine();
                Console.WriteLine();

                List<Expr> newlyReached = this.symbolicSuccessors(reached);
                List<Expr> newlyReachedFeasible = new List<Expr>();

                foreach (var t in newlyReached)
                {
                    // check to see if each element of newlyReached is satisfiable; if not, it's not needed
                    // (e.g., prestate is not satisfied: if a transition requires q_i = 0, but q_i = 1, don't include this)
                    if (Controller.Instance.Z3.checkTerm(t, out m, out core))
                    {
                        newlyReachedFeasible.Add(t);
                        TreeReach newt = new TreeReach(t, null);
                        reachset.Children.Add(newt);
                        toProcess.Add(newt);
                    }
                }

                Expr newlyReachedDisjunction = Controller.Instance.Z3.MkOr((BoolExpr[])newlyReachedFeasible.ToArray());

                // fixed point check (prove that the k^th iteration contains the k+1^st iteration)
                // unsat of: not (reach_{k+1} => reach_k) to prove reach_{k+1} \subseteq reach_k
                Console.WriteLine("Fixpoint check for iteration " + iteration.ToString());
                String nstr;
                if (Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies((BoolExpr)newlyReachedDisjunction, (BoolExpr)reached), out m, out core, out nstr, debug))
                //if (!Controller.Instance.Z3.checkTerm(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkImplies(newlyReachedDisjunction, reached)), debug))
                {
                    // safe
                    break;
                }
                Console.WriteLine();
                Console.WriteLine();

                // todo: convert to list / tree version
                reached = Controller.Instance.Z3.MkOr((BoolExpr)reached, (BoolExpr)newlyReachedDisjunction);
                //reached = Controller.Instance.Z3.Simplify(reached);

                toProcess.Remove(reachset); // remove the last processed value
                reachset = toProcess.ElementAt(0); // process the next one

                iteration++;
            }
            return true; // only break out of infinite loop if safe
        }

        /**
         * Compute the symbolic successors from a given symbolic formula over the system variables
         * 
         * From formula \phi(q) : Post(\phi(q)) = \exists q . T(q, q') and \phi(q)
         */
        public List<Expr> symbolicSuccessors(Expr prestate)
        {
            List<Expr> succs = new List<Expr>();

            foreach (Location la in this._cha.Locations)
            {
                foreach (Transition t in la.Transitions)
                {
                    // todo: just want to do this over the concrete system?

                    // todo: make sure we add the successor states due to discrete location changes to the terms...

                    Expr ts;
                    List<Expr> rel = new List<Expr>();
                    rel.Add(prestate);

                    // add the control location prestate from this location
                    rel.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Q["i"], Controller.Instance.Z3.MkInt(la.Value)));
                    rel.Add(t.ToTerm()); // add the control location post-state due to this transition

                    if (t.Guard != null)
                    {
                        List<Expr> allj = new List<Expr>();
                        allj.Add(Controller.Instance.Indices["j"]);
                        Expr g = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(Controller.Instance.Indices["i"], Controller.Instance.Indices["j"])), t.Guard);
                        g = Controller.Instance.Z3.MkForall(allj.ToArray(), g);
                        rel.Add(g);
                    }
                    if (t.Reset != null)
                    {
                        rel.Add(t.Reset);
                    }
                    ts = Controller.Instance.Z3.MkAnd((BoolExpr[])rel.ToArray());
                    //ts = Controller.Instance.Z3.Simplify(ts);

                    //Pattern[] pats = new Pattern[] { Controller.Instance.Z3.MkPattern(new Term[] { Controller.Instance.Indices["j"] }) };
                    List<Pattern> pats = new List<Pattern>();
                    List<String> names = new List<String>();
                    List<Sort> sorts = new List<Sort>();

                    // todo: change this and next loop to: foreach variable, extract type, add sort quantifier.
                    foreach (var pair in Controller.Instance.Q)
                    {
                        //pats.Add(Controller.Instance.Z3.MkPattern(new Term[] { pair.Value }));
                        //bound.Add(pair.Value);
                        //names.Add(pair.Key);
                        names.Add("q");
                        FuncDecl d = pair.Value.FuncDecl;
                        Symbol dn = d.Name;
                        Z3_decl_kind dk = d.DeclKind;
                        //sorts.Add(pair.Value.GetSort());
                        //TODO: Sort s = Controller.Instance.Z3.MkSort("(Int) " + pair.Value.GetSort().ToString()); // function sort: maps process indices to location type
                        //sorts.Add(s);

                        //sorts.Add(Controller.Instance.Z3.MkArraySort(Controller.Instance.IntType, Controller.Instance.RealType));
                        break;
                    }
                    foreach (var pair in Controller.Instance.IndexedVariables)
                    {
                        //pats.Add(Controller.Instance.Z3.MkPattern(new Term[] { pair.Value }));
                        //names.Add(pair.Key);
                        names.Add(pair.Key.Key);
                        //sorts.Add(pair.Value.GetSort());
                        //TODO: Sort s = Controller.Instance.Z3.MkSort("(Int) " + pair.Value.GetSort().ToString()); // function sort: maps process indices to variable type
                        // todo: add hash table to look up variable types
                        //sorts.Add(s);
                        break;
                    }
                    //TODO: ts = Controller.Instance.Z3.MkExists(sorts.ToArray(), names.ToArray(), ts);

                    List<Expr> bound = new List<Expr>();
                    foreach (var pair in Controller.Instance.Indices)
                    {
                        //pats.Add(Controller.Instance.Z3.MkPattern(new Term[] { pair.Value }));
                        bound.Add(pair.Value);
                    }
                    ts = Controller.Instance.Z3.MkExists(bound.ToArray(), ts);
                    //TODO: ts = Controller.Instance.Z3.Simplify(ts);

                    // unprime all variables
                    foreach (var pair in Controller.Instance.QPrimed)
                    {
                        Controller.Instance.Z3.replaceTerm(ref ts, ts, pair.Value, Controller.Instance.Q[pair.Key], true);
                    }
                    foreach (var pair in Controller.Instance.IndexedVariablesPrimed)
                    {
                        Controller.Instance.Z3.replaceTerm(ref ts, ts, pair.Value, Controller.Instance.IndexedVariables[new KeyValuePair<String, String>(pair.Key.Key.Replace("'", ""), pair.Key.Value)], true);
                    }
                    //ts = Controller.Instance.Z3.Simplify(ts);
                    succs.Add(ts);
                }
                //}
            }
            return succs;
        }

        /**
         * Generate predicates to use in the abstraction
         */
        private void makePredicates()
        {
            this.Predicates = new HashSet<Expr>();

            // add a predicate for each property specified and its negation
            foreach (Property p in this._cha.Parent.Properties)
            {
                if (p.Formula != null && !this.Predicates.Contains(p.Formula))
                {
                    // heuristic: only add new predicates (search by string, not by object)
                    foreach (Expr t in this.Predicates)
                    {
                        if (t.ToString() == p.Formula.ToString())
                        {
                            continue;
                        }
                    }
                    // copy the guard and its negation to a list, which we will then iterate over to create the entire abstract state space
                    //this.Predicates.Add(p.Formula);
                    //this.Predicates.Add(Controller.Instance.Z3.MkNot(p.Formula)); // todo: try this
                    this._r += 1; // only count the predicate
                }
            }

            // add a predicate for every guard and its negation
            foreach (ConcreteLocation l in this._cha.Locations)
            {
                foreach (Transition t in l.Transitions)
                {
                    // predicate abstraction: for each guard, take predicates as the guard and its negation
                    // heuristic: only add new predicates
                    if (t.Guard != null && !this.Predicates.Contains(t.Guard))
                    {
                        // heuristic: only add new predicates (search by string, not by object)
                        foreach (Expr p in this.Predicates)
                        {
                            if (p.ToString() == t.Guard.ToString())
                            {
                                continue;
                            }
                        }
                        // copy the guard and its negation to a list, which we will then iterate over to create the entire abstract state space
                        this.Predicates.Add(t.Guard);
                        //this.Predicates.Add(Controller.Instance.Z3.MkNot(t.Guard)); // todo: try this out?

                        this._r += 1; // only count the predicate
                    }
                    // todo: need to add conjunction of all predicates after doing this...
                }
                // add a predicate for every control location (so we can easily count the number of processes in each location)
                //this.Predicates.Add(l.StatePredicate); // todo: try this out?
            }
        }

        /**
         * Create the abstract state space given an indexed hybrid automaton
         */
        private void makeAbstractStateSpace()
        {
            this._S = this._cha.Locations.Count; // number of discrete locations
            this._r = 0; // number of inter-predicates
            this._T = 0;
            this._variables = this._cha.Variables;

            if (this.Predicates == null)
            {
                throw new Exception("Error generating abstract state space, no predicates were specified to be used in the abstraction.");
            }

            IEnumerable<Location> query = this._cha.Locations.OrderBy(loc => loc.Value);
            foreach (Location lref in query)
            {
                List<EnvironmentState> es = new List<EnvironmentState>();
                foreach (Location lenv in query)
                {
                    foreach (Expr p in this.Predicates)
                    {
                        EnvironmentState q = new EnvironmentState(lenv.Label, lenv.Value, 0, p);
                        q.VariableRates = lenv.VariableRates; // copy variable rates (for timed transitions)
                        es.Add(q);
                        this._T += 1;
                    }
                }

                // finish enumerating states by adding a copy of es for each control location of the reference process
                this._states.Add(new AbstractState((ConcreteLocation)lref, es));
            }
        }

        /**
         * Generate all valuations of the abstract state space
         * Used for explicit state model checking output (e.g., PHAVer)
         */
        private void makeAbstractStateValuations()
        {
            foreach (AbstractState a in this._states)
            {
                for (UInt64 i = 0; i < Math.Pow(4, a.EnvironmentStates.Count); i++) // todo: change 4 to: cardinality of {None, All, AllButOne, One, \ldots, Cutoff}
                {
                    Expr p = Controller.Instance.Z3.MkTrue();
                    AbstractState ac = ((AbstractState)a.Clone());

                    for (int j = 0; j < a.EnvironmentStates.Count; j++)
                    {
                        switch (i % 4)
                        {
                            case 0:
                                ac.EnvironmentStates.ElementAt(j).Count = Counter.None;
                                break;
                            case 1:
                                ac.EnvironmentStates.ElementAt(j).Count = Counter.One;
                                break;
                            case 2:
                                ac.EnvironmentStates.ElementAt(j).Count = Counter.AllButOne;
                                break;
                            case 3:
                                ac.EnvironmentStates.ElementAt(j).Count = Counter.All;
                                break;
                            default:
                                break;
                        }

                        // convert integer to boolean representation by bit-shifting
                        //if (((i >> j) & 0x01) == 0)
                        //{
                            //ac.EnvironmentStates.ElementAt(j).State = true; // todo: set value if need to generate all valuations
                            p = Controller.Instance.Z3.MkAnd(p, ac.EnvironmentStates.ElementAt(j).EnvironmentPredicate);
                        //}
                        //else
                        //{
                        //  ac.EnvironmentStates.ElementAt(j).State = false; // todo: set value if need to generate all valuations

                        //    p = Controller.Instance.Z3.MkAnd(p, Controller.Instance.Z3.MkNot(ac.EnvironmentStates.ElementAt(j).EnvironmentPredicate));
                        //}
                    }

                    // prune infeasible state space: if combined predicate can be satisfied, add it
                    // todo: need proof of soundness while doing such pruning
                    //       note that this prevents the environment process from being in two locations simultaneously---is this okay? seems like we might allow this
                    //       if this is okay, then just use the intra-predicate predicate (.predicate) and not the environment predicate (.envpred) (doing this for now for testing)
                    Model m = null;
                    Expr[] core;
                    if (Controller.Instance.Z3.checkTerm(p, out m, out core) && !ac.Concretization().ToString().Equals("false"))
                    {
                        this._valuations.Add(ac);
                    }
                    else
                    {
                        ac.Dispose();
                    }
                }
            }
        }

        #region unused


        /**
         * From formula \phi(q) : Pre(\phi(q)) = \exists q' . T(q, q') and \phi(q')
         * Replace all q terms in \phi by q'
         */
        public List<Expr> symbolicPredecessors(Expr phi)
        {
            List<Expr> pred = new List<Expr>();
            // todo
            return pred;
        }

        /**
         * Create the abstract transition relation
         */
        private void makeAbstractTransitions()
        {
            // blocking set for reference process
            // compute block set as: for every guarded transition with guard G(i,j), for every environment predicate (i.e., the tuple e_a), check if e_a(i,j) => !G(i,j)
            foreach (ConcreteLocation cl in _cha.Locations)
            {
                foreach (Transition t in cl.Transitions)
                {
                    foreach (AbstractState sa in this._valuations)
                    {
                        foreach (EnvironmentState ea in sa.EnvironmentStates)
                        {
                            continue;
                            // control location change only (no data variable changes)
                            if (t.Guard != null && t.Reset == null)
                            {
                                // reference process block set (use predicate, not environmentpredicate which also has control location information)
                                Expr ts = Controller.Instance.Z3.MkImplies(ea.Predicate, Controller.Instance.Z3.MkNot(t.Guard));
                                Model m = null;
                                Expr[] core;
                                if (Controller.Instance.Z3.checkTerm(ts, out m, out core))
                                {
                                    t.addBlockingRef(ea.Predicate);
                                }
                                /*
                                foreach (AAbstractState sb in this._valuations)
                                {
                                    foreach (EnvironmentState eb in sb.EnvironmentStates)
                                    {
                                        Term ebp = eb.Predicate;
                                        ebp = replaceIndices(ebp, new Term[] { Controller.Instance.j_idx }, new Term[] { Controller.Instance.k_idx }); // switch eb.predicate to E(i, k)

                                        // environment block set due to environment condition (compare env predicate and predicate)
                                        ts = Controller.Instance.Z3.MkAnd(ea.EnvironmentPredicate, ebp);

                                        Term gjk = t.Guard;
                                        gjk = replaceIndices(gjk, new Term[] { Controller.Instance.i_idx, Controller.Instance.j_idx }, new Term[] { Controller.Instance.j_idx, Controller.Instance.k_idx }); // switch eb.predicate to E(i, k)
                                        ts = Controller.Instance.Z3.MkImplies(ts, Controller.Instance.Z3.MkNot(gjk)); // switch guard to G(j, k) from G(i, j)
                                        if (this.checkTerm(ts))
                                        {
                                            t.addBlockingEnvEC(eb.Predicate);
                                        }

                                        // environment block set due to reference process state
                                        ts = Controller.Instance.Z3.MkAnd(ea.EnvironmentPredicate, sb.ReferenceState.StatePredicate);

                                        Term tg = t.Guard;
                                        tg = replaceIndices(tg, new Term[] { Controller.Instance.i_idx, Controller.Instance.j_idx }, new Term[] { Controller.Instance.j_idx, Controller.Instance.i_idx });

                                        ts = Controller.Instance.Z3.MkImplies(ts, Controller.Instance.Z3.MkNot(tg));
                                        
                                        if (this.checkTerm(ts))
                                        {
                                            t.addBlockingEnvCL(ea.EnvironmentPredicate);
                                        }
                                    }
                                }*/
                            }
                            // reference process data variable change
                            else if (t.Guard != null && t.Reset != null)
                            {
                                Expr tt = Controller.Instance.Z3.MkAnd((BoolExpr)t.Guard, (BoolExpr)t.Reset);
                                //Term tf = Controller.Instance.Z3.MkAnd( Controller.Instance.Z3.MkNot(t.Guard), t.Reset);
                                Expr tf = Controller.Instance.Z3.MkNot((BoolExpr)t.Guard);

                                Expr tu = Controller.Instance.Z3.MkOr((BoolExpr)tt, (BoolExpr)tf);

                                Expr tg = Controller.Instance.Z3.MkAnd((BoolExpr)tu, (BoolExpr)ea.EnvironmentPredicate);

                                Model m = null;
                                Expr[] core;
                                if (Controller.Instance.Z3.checkTerm(tg, out m, out core))
                                {
                                    Console.WriteLine("Satisfiable: " + tg.ToString());
                                }
                            }
                        }
                    }
                }
            }

            // for each pair <sa, sb> of abstract states, determine if there is an edge from ea to eb
            foreach (AbstractState sa in this._valuations)
            {
                foreach (EnvironmentState ea in sa.EnvironmentStates)
                {
                    foreach (AbstractState sb in this._valuations)
                    {
                        foreach (EnvironmentState eb in sb.EnvironmentStates)
                        {
                            foreach (Transition t in sa.ReferenceState.Transitions)
                            {
                                List<Expr> rel = new List<Expr>();
                                rel.Add(sa.Concretization());
                                rel.Add(sb.ConcretizationPrimed());
                                if (t.Guard != null)
                                {
                                    List<Expr> allj = new List<Expr>();
                                    allj.Add(Controller.Instance.Indices["j"]);
                                    Expr g = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(Controller.Instance.Indices["i"], Controller.Instance.Indices["j"])), t.Guard);
                                    //Term g = t.Guard;
                                    g = Controller.Instance.Z3.MkForall(allj.ToArray(), g);
                                    rel.Add(g);
                                }
                                if (t.Reset != null)
                                {
                                    rel.Add(t.Reset);
                                }
                                Expr ts = Controller.Instance.Z3.MkAnd((BoolExpr[])rel.ToArray());
                                //ts = Controller.Instance.Z3.Simplify(ts);


                                //Pattern[] pats = new Pattern[] { Controller.Instance.Z3.MkPattern(new Term[] { Controller.Instance.Indices["j"] }) };
                                List<Pattern> pats = new List<Pattern>();
                                List<Expr> bound = new List<Expr>();
                                foreach (var pair in Controller.Instance.Indices)
                                {
                                    //pats.Add(Controller.Instance.Z3.MkPattern(new Term[] { pair.Value }));
                                    bound.Add(pair.Value);
                                }
                                foreach (var pair in Controller.Instance.Q)
                                {
                                    //pats.Add(Controller.Instance.Z3.MkPattern(new Term[] { pair.Value }));
                                    bound.Add(pair.Value);
                                }
                                foreach (var pair in Controller.Instance.IndexedVariables)
                                {
                                    //pats.Add(Controller.Instance.Z3.MkPattern(new Term[] { pair.Value }));
                                    bound.Add(pair.Value);
                                }
                                ts = Controller.Instance.Z3.MkExists(0, bound.ToArray(), null, ts);
                                //ts = Controller.Instance.Z3.Simplify(ts);

                                Model m = null;
                                Expr[] core;
                                if (Controller.Instance.Z3.checkTerm(ts, out m, out core))
                                {
                                    sa.addTransition(new Transition(sb, Transition.AbstractTransitionType.ref_ctrl));
                                }

                                //if (Controller.Instance.Z3.MkAnd(sa.Concretization())


                                continue;
                                // reference process control location change
                                // 1. concrete transition can go to sb
                                // 2. blocking set for reference process has all corresponding e_i == 0
                                if (t.Guard != null && t.Reset == null && t.NextStates.Contains(sb.ReferenceState) && t.BlockingSetRef.Contains(ea.Predicate) && ea.Count == Counter.None)
                                {
                                    sa.addTransition(new Transition(sb, Transition.AbstractTransitionType.ref_ctrl));
                                }
                                // no guard on the transition, i.e., the transition has a guard of the form: "\forall otr \neq slf . true", so just add an edge for this one
                                else if (t.Guard == null && t.Reset == null && t.NextStates.Contains(sb.ReferenceState))
                                {
                                    sa.addTransition(new Transition(sb, Transition.AbstractTransitionType.ref_ctrl));
                                }

                                // time transition
                                if (!((sa.ReferenceState.VariableRates != null) && ((ea.VariableRates != null) && ea.Count >= Counter.One))) // if both are in a state where time can flow, since we assume timed for now, then the predicates never change valuation.
                                {
                                    if (sa.ReferenceState.VariableRates != null)
                                    {
                                        foreach (Variable v in this._cha.Variables)
                                        {
                                            if (sa.ReferenceState.VariableRates.ContainsKey(v))
                                            {
                                                // if vars + dynamics can yield state sb /\ eb...
                                                sa.addTransition(new Transition(sb, Transition.AbstractTransitionType.time));
                                            }
                                        }
                                    }

                                    if (ea.VariableRates != null && ea.Count >= Counter.One)
                                    {
                                        foreach (Variable v in this._cha.Variables)
                                        {
                                            if (ea.VariableRates.ContainsKey(v))
                                            {
                                                // if vars + dynamics can yield state sb /\ eb...
                                                sa.addTransition(new Transition(sb, Transition.AbstractTransitionType.time));
                                            }
                                        }
                                    }
                                }

                                /*
                                // assert the pre-state (i.e., we know state sa holds if we're looking at a transition from it)
                                Term[] preArray = { sa.ReferenceState.StatePredicate, ea.EnvironmentPredicate };
                                Term prestate = Controller.Instance.Z3.MkAnd(preArray);
                                Term[] postArray = {sb.ReferenceState.StatePredicate, eb.EnvironmentPredicate};
                                Term poststate = Controller.Instance.Z3.MkAnd(postArray);

                                //Term checking = Controller.Instance.Z3.MkAnd(t.Guard);
                                Term guard;
                                if (t.Guard != null)
                                {
                                    guard = t.Guard;
                                }
                                else
                                {
                                    continue;
                                }

                                // if statement is valid, then create a transition
                                if (this.existsAbstractTransition(prestate, guard, poststate))
                                {
                                    sa.Transitions.Add(new Transition(sb));
                                }
                                 * */
                            }
                        }
                    }
                }
            }
        }

        #endregion
    }
}
