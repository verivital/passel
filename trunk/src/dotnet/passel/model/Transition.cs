using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    public class Transition
    {
        public enum AbstractTransitionType { ref_ctrl, env_ctrl, ref_data, env_data, time };


        public static Transition TimeTransition = new Transition();

        public Expr Guard;
        protected Expr _reset;
        protected List<AState> _nextStates;
        protected List<Expr> _blockingSetRef;
        protected List<Expr> _blockingSetEnvEC;
        protected List<Expr> _blockingSetEnvCL;
        protected AbstractTransitionType _type;

        private ConcreteLocation _parent;

        public BoolExpr TransitionTerm;

        public List<String> Indices = new List<string>();

        public ConcreteLocation Parent
        {
            get { return this._parent; }
            set {
                this._parent = value;
                Expr hidxinner = Controller.Instance.Z3.MkIntConst("h");
                this.TransitionTermGlobal = (BoolExpr)this.makeTransitionTerm(null, hidxinner, null); // no local vars
                this.TransitionTerm = (BoolExpr)this.makeTransitionTerm(value, hidxinner, null); // with local vars
            }
        }

        public BoolExpr TransitionTermGlobal;

        public Transition()
        {
        }

        public Transition(ConcreteLocation p)
        {
            this.Parent = p;

            // todo next: switch if not int type: , Controller.Instance.IndexType
            Expr hidxinner = Controller.Instance.Z3.MkIntConst("h");
            this.TransitionTermGlobal = (BoolExpr)this.makeTransitionTerm(null, hidxinner, null); // no local vars
            this.TransitionTerm = (BoolExpr)this.makeTransitionTerm(this.Parent, hidxinner, null); // with local vars
        }
        
        public Transition(ConcreteLocation p, AState nextState) : this(p)
        {
            this._nextStates = new List<AState>();
            this._nextStates.Add(nextState);
        }

        public Transition(ConcreteLocation p, AState nextState, AbstractTransitionType t)
            : this(p, nextState)
        {
            this._type = t;
        }

        public Transition(ConcreteLocation p, List<AState> nextStates) : this(p)
        {
            this._nextStates = nextStates;
        }

        public Transition(ConcreteLocation p, Expr guard, Expr reset) : this(p)
        {
            this.Guard = guard;
            this._reset = reset;
        }

        public Transition(ConcreteLocation p, Expr guard, Expr reset, AState nextState)
            : this(p, nextState)
        {
            this.Guard = guard;
            this._reset = reset;
        }

        public Transition(ConcreteLocation p, Expr guard, Expr reset, List<AState> nextStates)
            : this(p, nextStates)
        {
            this.Guard = guard;
            this._reset = reset;
        }

        public String ToString()
        {
            if (TransitionTerm == null)
            {
                return "time_flow";
            }
            else
            {
                return this.TransitionTerm.ToString();
            }
        }

        /*public Expr Guard
        {
            get { return this._guard; }
            set { this._guard = value; }
        }*/

        public Expr Reset
        {
            get { return this._reset; }
            set { this._reset = value; }
        }

        public AbstractTransitionType Type
        {
            get { return this._type; }
            set { this._type = value; }
        }

        /**
         * Create a term corresponding to the next states (disjunction)
         */
        public Expr ToTerm()
        {
            List<BoolExpr> post = new List<BoolExpr>();
            foreach (AState l in this._nextStates)
            {
                //post.Add(Controller.Instance.Z3.MkEq(Controller.Instance.QPrimed["i"], Controller.Instance.Z3.MkConst(l.Value.ToString(), Controller.Instance.LocType)));
                post.Add(Controller.Instance.Z3.MkEq(Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>("q" + Controller.PRIME_SUFFIX, "i")], Controller.Instance.Z3.MkConst(l.Label, Controller.Instance.LocType)));
            }
            if (post.Count > 1)
            {
                return Controller.Instance.Z3.MkOr(post.ToArray());
            }
            else if (post.Count == 1)
            {
                return post.First();
            }
            else // shouldn't ever call this (Count = 0 shouldn't be used), but true should be identity anywhere this is used
            {
                return Controller.Instance.Z3.MkTrue();
            }
        }

        public Expr UGuard = null;

        public List<AState> NextStates
        {
            get
            {
                if (this._nextStates == null)
                {
                    this._nextStates = new List<AState>();
                }
                return this._nextStates;
            }
            set { this._nextStates = value; }
        }

        public void addNextState(AState nextState)
        {
            this._nextStates.Add(nextState);
        }

        public List<Expr> BlockingSetRef
        {
            get
            {
                if (this._blockingSetRef == null)
                {
                    this._blockingSetRef = new List<Expr>();
                }
                return this._blockingSetRef;
            }
            set { this._blockingSetRef = value; }
        }

        public List<Expr> BlockingSetEnvEC
        {
            get
            {
                if (this._blockingSetEnvEC == null)
                {
                    this._blockingSetEnvEC = new List<Expr>();
                }
                return this._blockingSetEnvEC;
            }
            set { this._blockingSetEnvEC = value; }
        }

        public List<Expr> BlockingSetEnvCL
        {
            get
            {
                if (this._blockingSetEnvCL == null)
                {
                    this._blockingSetEnvCL = new List<Expr>();
                }
                return this._blockingSetEnvCL;
            }
            set { this._blockingSetEnvCL = value; }
        }

        public void addBlockingRef(Expr b)
        {
            if (this._blockingSetRef == null)
            {
                this._blockingSetRef = new List<Expr>();
            }
            // unique add
            if (!this._blockingSetRef.Contains(b))
            {
                this._blockingSetRef.Add(b);
            }
        }

        public void addBlockingEnvEC(Expr b)
        {
            if (this._blockingSetEnvEC == null)
            {
                this._blockingSetEnvEC = new List<Expr>();
            }
            // unique add
            if (!this._blockingSetEnvEC.Contains(b))
            {
                this._blockingSetEnvEC.Add(b);
            }
        }

        public void addBlockingEnvCL(Expr b)
        {
            if (this._blockingSetEnvCL == null)
            {
                this._blockingSetEnvCL = new List<Expr>();
            }
            // unique add
            if (!this._blockingSetEnvCL.Contains(b))
            {
                this._blockingSetEnvCL.Add(b);
            }
        }

        public Expr MakeReset(Expr idx, uint N, uint k)
        {
            ConcreteLocation l = this.Parent;

            List<BoolExpr> resets = new List<BoolExpr>();

            if (this.NextStates.Count > 0)
            {
                resets.Add((BoolExpr)this.ToTerm());       // discrete location post-state (e.g., loc'[i] = 2)
            }

            List<String> globalVariableResets = new List<String>(); // global variables not reset
            List<String> indexVariableResets = new List<String>();  // indexed variables of process moving that are not reset
            List<String> universalIndexVariableResets = new List<String>();  // universally quantified indexed variables that are reset

            if (this.Reset != null)
            {
                resets.Add((BoolExpr)this.Reset);

                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(this.Reset);
                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(this.Reset);
            }
            else
            {
                // global variable was not mentioned since reset is null: add it to the identity global variables (g' = g)
                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(null);
                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(null);
            }

            if (this.UGuard != null)
            {
                universalIndexVariableResets = Controller.Instance.Z3.findIndexedVariableResetsNeg(this.UGuard);
            }

            Expr resetAnd = null;
            // create conjunction of pre-state and post-state conditions
            if (resets.Count > 0)
            {
                resetAnd = Controller.Instance.Z3.MkAnd(resets.ToArray());
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
                        delegate(Variable gv)
                        {
                            return gv.Name == v.Key;
                        }).Type == Variable.VarType.index && Controller.Instance.Z3.findTerm(this.Reset, v.Value, true))
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
                identity = Controller.Instance.Sys.forallIdentity(gidx, globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N); // no process moves if no location
            }
            else
            {
                identity = Controller.Instance.Sys.forallIdentity(idx, globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N);
            }

            if (resetAnd == null && N == 0)
            {
                resetAnd = identity;
            }
            else if (N == 0)
            {
                resetAnd = Controller.Instance.Z3.MkAnd((BoolExpr)resetAnd, (BoolExpr)identity);
            }

            
            List<BoolExpr> transAll = new List<BoolExpr>();
            // expand quantifier manually
            for (uint i = 1; i <= N; i++)
            {
                Expr numidx = Controller.Instance.Z3.MkInt(i);
                //Expr trans = locInvariantAnd.Substitute(idx, numidx); // instantiate i
                //transAll.Add(z3.MkAnd(z3.MkEq(idx, numidx), (BoolExpr)locInvariantAnd)); // simply set symbol idx = value idx
                BoolExpr copy = (BoolExpr)Controller.Instance.Z3.copyExpr(resetAnd);

                idx = Controller.Instance.Z3.MkIntConst("i");

                foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables) // TODO: generalize
                {
                    //copy.Substitute(z3.MkApp(v.Value, idx), z3.MkApp(v.Value, numidx)); // substitute to function
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.IndexedVariables[new KeyValuePair<string,string>(v.Name, idx.ToString())], Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k, i)]); // substitute to constant (needed for doing q.e.)
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>(v.Name + Controller.PRIME_SUFFIX, idx.ToString())], Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k + 1, i)]); // substitute to constant (needed for doing q.e.)
                }
                copy = (BoolExpr)copy.Substitute(idx, numidx); // must be outside loop
                copy = Controller.Instance.Z3.MkAnd(copy, (BoolExpr)Controller.Instance.Sys.forallIdentity(Controller.Instance.Z3.MkInt(i), globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N));

                foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables) // TODO: generalize
                {
                    //copy.Substitute(z3.MkApp(v.Value, idx), z3.MkApp(v.Value, numidx)); // substitute to function
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Z3.MkInt(i)), Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k, i)]); // substitute to constant (needed for doing q.e.)
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.Z3.MkApp(v.ValuePrimed, Controller.Instance.Z3.MkInt(i)), Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k + 1, i)]); // substitute to constant (needed for doing q.e.)
                }

                // todo: check order of operations
                foreach (var v in Controller.Instance.Sys.Variables)
                {
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.Sys.GlobalReachValues[new Tuple<string, uint>(v.Name, k)]); // substitute to constant (needed for doing q.e.)
                    copy = (BoolExpr)copy.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Name], Controller.Instance.Sys.GlobalReachValues[new Tuple<string, uint>(v.Name, k + 1)]); // substitute to constant (needed for doing q.e.)
                }

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
                }
                transAll.Add(copy);
            }
            resetAnd = Controller.Instance.Z3.MkOr(transAll.ToArray());
            return resetAnd;
        }

        /// <summary>
        /// Return true if transition is enabled from state pre
        /// </summary>
        /// <param name="pre"></param>
        /// <returns></returns>
        public Boolean IsEnabled(Expr pre)
        {
            Expr tt = this.makeTransitionTerm(this.Parent, Controller.Instance.Indices["i"]);
            Expr enabled = Controller.Instance.Z3.MkAnd((BoolExpr)pre, (BoolExpr)tt);
            return Controller.Instance.Z3.checkTerm(enabled);
        }

        /// <summary>
        /// Returns true if the transition modifies any global variables
        /// </summary>
        /// <returns></returns>
        public Boolean HasGlobalReset()
        {
            if (this.Reset != null)
            {
                foreach (var v in Controller.Instance.GlobalVariables.Keys)
                {
                    // nasty hack, but probably fast way to do this
                    if (this.Reset.ToString().Contains(v + Controller.PRIME_SUFFIX))
                    {
                        return true;
                    }
                }
            }
            return false;
        }

        // todo: performance versus just keeping local copy in each transition?
        private static Dictionary<KeyValuePair<Transition, Expr>, Expr> CachePost = new Dictionary<KeyValuePair<Transition, Expr>, Expr>();

        /// <summary>
        /// Compute post from pre
        /// </summary>
        /// <param name="pre"></param>
        /// <returns></returns>
        public Expr MakePost(Expr pre)
        {
            KeyValuePair<Transition, Expr> postKey = new KeyValuePair<Transition, Expr>(this, pre);
            if (Transition.CachePost.ContainsKey(postKey))
            {
                return CachePost[postKey];
            }

            Expr idx = Controller.Instance.Indices["i"];

            ConcreteLocation l = this.Parent;

            List<BoolExpr> resets = new List<BoolExpr>();

            resets.Add((BoolExpr)pre); // add prestate

            if (this.NextStates.Count > 0)
            {
                resets.Add((BoolExpr)this.ToTerm());       // discrete location post-state (e.g., loc'[i] = 2)
            }

            List<String> globalVariableResets = new List<String>(); // global variables not reset
            List<String> indexVariableResets = new List<String>();  // indexed variables of process moving that are not reset
            List<String> universalIndexVariableResets = new List<String>();  // universally quantified indexed variables that are reset

            if (this.Reset != null)
            {
                resets.Add((BoolExpr)this.Reset);

                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(this.Reset);
                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(this.Reset);
            }
            else
            {
                // global variable was not mentioned since reset is null: add it to the identity global variables (g' = g)
                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(null);
                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(null);
            }

            if (this.UGuard != null) // TODO: handle univerasl resets (assume none for now)
            {
                universalIndexVariableResets = Controller.Instance.Z3.findIndexedVariableResetsNeg(this.UGuard);
            }

            Expr resetAnd = null;
            // create conjunction of pre-state and post-state conditions
            if (resets.Count > 0)
            {
                resetAnd = Controller.Instance.Z3.MkAnd(resets.ToArray());
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
                        delegate(Variable gv)
                        {
                            return gv.Name == v.Key;
                        }).Type == Variable.VarType.index && Controller.Instance.Z3.findTerm(this.Reset, v.Value, true))
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
                identity = Controller.Instance.Sys.forallIdentityPost(gidx, globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, 0); // no process moves if no location
            }
            else
            {
                identity = Controller.Instance.Sys.forallIdentityPost(idx, globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, 0);
            }

            resetAnd = Controller.Instance.Z3.MkAnd((BoolExpr)resetAnd, (BoolExpr)identity);
            resetAnd = Controller.Instance.Z3.copyExpr(resetAnd);

            // short circuit
            /*
            if (this.Reset == null && Controller.Instance.Sys.Variables.Count == 0)
            {
                return resetAnd;
            }
             */

            // replace all function declarations with constants (e.g., (q i) => (qi), where qi is a constant, instead of a function)

            List<Expr> bound = new List<Expr>();

            // TODO: use this.Parent.Parent.Parent, etc to access hybrid automata, holism, etc (will make generalizing to compositions easier)
            foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
            {
                Expr varConst = Controller.Instance.Z3.MkConst(v.Name + "_" + "i", v.TypeSort);
                Expr varConstPost = Controller.Instance.Z3.MkConst(v.NamePrimed + "_" + "i", v.TypeSort);
                resetAnd = resetAnd.Substitute(Controller.Instance.Z3.MkApp(v.Value, idx), varConst);
                resetAnd = resetAnd.Substitute(Controller.Instance.Z3.MkApp(v.ValuePrimed, idx), varConstPost);
                bound.Add(varConst);
            }

            foreach (var v in Controller.Instance.GlobalVariables.Values)
            {
                bound.Add(v);
            }


            //Expr post = Controller.Instance.Z3.MkExists(new Expr[] { idx }, (BoolExpr)resetAnd);
            Expr post = Controller.Instance.Z3.MkExists(bound.ToArray(), (BoolExpr)resetAnd);


            // HACK: replace all location names with their values...
            foreach (var loc in Controller.Instance.Sys.HybridAutomata[0].Locations)
            {
                post = post.Substitute(loc.LabelExpr, loc.BitVectorExpr);
            }
            post = post.Substitute(Controller.Instance.IndexN, Controller.Instance.Z3.MkInt(Controller.Instance.IndexNValue));



            Tactic tqe = Controller.Instance.Z3.Repeat(Controller.Instance.Z3.MkTactic("qe"));
            Goal g = Controller.Instance.Z3.MkGoal();




            List<BoolExpr> remAss = Controller.Instance.Z3.Assumptions.FindAll(a => a.IsQuantifier); // todo: add type constraints to constant (q_i) instead of functions (q i)
            Controller.Instance.Z3.Assumptions.RemoveAll(a => a.IsQuantifier); // otherwise q.e. will fail
            g.Assert(Controller.Instance.Z3.Assumptions.ToArray());
            Controller.Instance.Z3.Assumptions.AddRange(remAss); // add back
            g.Assert(Controller.Instance.Z3.AssumptionsUniversal.ToArray());




            g.Assert((BoolExpr)post);
            g = g.Simplify();
            ApplyResult ar = tqe.Apply(g);

            List<BoolExpr> postStates = new List<BoolExpr>();
            foreach (var sg in ar.Subgoals)
            {
                postStates.AddRange(sg.Formulas);
            }



            postStates.RemoveAll(fa => Controller.Instance.Z3.Assumptions.Contains(fa));
            postStates.RemoveAll(fa => Controller.Instance.Z3.AssumptionsUniversal.Contains(fa));
            




            post = Controller.Instance.Z3.MkAnd(postStates.ToArray());


            // HACK: replace all location values with their names...
            foreach (var loc in Controller.Instance.Sys.HybridAutomata[0].Locations)
            {
                post = post.Substitute(loc.BitVectorExpr, loc.LabelExpr);
            }

            // convert constants back to functions
            foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
            {
                Expr varConst = Controller.Instance.Z3.MkConst(v.Name + "_" + "i", v.TypeSort);
                Expr varConstPost = Controller.Instance.Z3.MkConst(v.NamePrimed + "_" + "i", v.TypeSort);
                post = post.Substitute(varConst, Controller.Instance.Z3.MkApp(v.Value, idx));
                post = post.Substitute(varConstPost, Controller.Instance.Z3.MkApp(v.ValuePrimed, idx));
            }
            
            Controller.Instance.Z3.unprimeAllVariables(ref post); // unprime

            System.Console.WriteLine("POST: " + post.ToString());

            // cache result
            CachePost.Add(postKey, post);

            return post;
        }




        /**
         * Make terms corresponding to pre and post-state for a transition (can be local or global transition)
         */
        public Expr makeTransitionTerm(ConcreteLocation l, Expr idx, params uint[] paramList)
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
            if (this.NextStates.Count > 0)
            {
                locInvariant.Add((BoolExpr)this.ToTerm());       // discrete location post-state (e.g., loc'[i] = 2)
            }

            // add guard, if one exists
            if (this.Guard != null)
            {
                locInvariant.Add((BoolExpr)this.Guard);
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

            if (this.Reset != null)
            {
                locInvariant.Add((BoolExpr)this.Reset);

                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(this.Reset);
                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(this.Reset);
            }
            else
            {
                // global variable was not mentioned since reset is null: add it to the identity global variables (g' = g)
                globalVariableResets = Controller.Instance.Z3.findGlobalVariableResets(null);
                indexVariableResets = Controller.Instance.Z3.findIndexedVariableResets(null);
            }

            if (this.UGuard != null)
            {
                universalIndexVariableResets = Controller.Instance.Z3.findIndexedVariableResetsNeg(this.UGuard);
            }

            Expr locInvariantAnd = null;
            // create conjunction of pre-state and post-state conditions
            if (locInvariant.Count > 0)
            {
                locInvariantAnd = Controller.Instance.Z3.MkAnd(locInvariant.ToArray());
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
                        delegate(Variable gv)
                        {
                            return gv.Name == v.Key;
                        }).Type == Variable.VarType.index && Controller.Instance.Z3.findTerm(this.Reset, v.Value, true))
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
                identity = Controller.Instance.Sys.forallIdentity(gidx, globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N); // no process moves if no location
            }
            else
            {
                identity = Controller.Instance.Sys.forallIdentity(idx, globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N);
            }

            if (locInvariantAnd == null && N == 0)
            {
                locInvariantAnd = identity;
            }
            else if (N == 0)
            {
                locInvariantAnd = Controller.Instance.Z3.MkAnd((BoolExpr)locInvariantAnd, (BoolExpr)identity);
            }

            if (l != null && N == 0)
            {
                locInvariantAnd = locInvariantAnd.Substitute(Controller.Instance.Indices["i"], idx); // replace i by h

                BoolExpr idxConstraint = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)idx, (ArithExpr)Controller.Instance.IntOne), Controller.Instance.Z3.MkLe((ArithExpr)idx, (ArithExpr)Controller.Instance.IndexN));

                // add quantifiers based on pre-state and post-state, using implies vs. and options and indexing options
                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.naturalOneToN:
                        switch (Controller.Instance.ExistsOption)
                        {
                            case Controller.ExistsOptionType.and:
                                locInvariantAnd = Controller.Instance.Z3.MkAnd(idxConstraint, (BoolExpr)locInvariantAnd); // 1 <= h <= N, enforce identity for all other processes not moving
                                break;
                            case Controller.ExistsOptionType.implies:
                            default:
                                locInvariantAnd = Controller.Instance.Z3.MkImplies(idxConstraint, (BoolExpr)locInvariantAnd); // 1 <= h <= N, enforce identity for all other processes not moving
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
                    Expr numidx = Controller.Instance.Z3.MkInt(i);
                    //Expr trans = locInvariantAnd.Substitute(idx, numidx); // instantiate i
                    //transAll.Add(z3.MkAnd(z3.MkEq(idx, numidx), (BoolExpr)locInvariantAnd)); // simply set symbol idx = value idx
                    BoolExpr copy = (BoolExpr)Controller.Instance.Z3.copyExpr(locInvariantAnd);

                    foreach (var v in Controller.Instance.Sys.Variables)
                    {
                        copy = (BoolExpr)copy.Substitute(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.Sys.GlobalReachValues[new Tuple<string, uint>(v.Name, k)]); // substitute to constant (needed for doing q.e.)
                        copy = (BoolExpr)copy.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Name], Controller.Instance.Sys.GlobalReachValues[new Tuple<string, uint>(v.Name, k + 1)]); // substitute to constant (needed for doing q.e.)
                    }

                    foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables) // TODO: generalize
                    {
                        //copy.Substitute(z3.MkApp(v.Value, idx), z3.MkApp(v.Value, numidx)); // substitute to function
                        idx = Controller.Instance.Z3.MkIntConst("i");
                        copy = (BoolExpr)copy.Substitute(Controller.Instance.Z3.MkApp(v.Value, idx), Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k, i)]); // substitute to constant (needed for doing q.e.)
                        copy = (BoolExpr)copy.Substitute(Controller.Instance.Z3.MkApp(v.ValuePrimed, idx), Controller.Instance.Sys.ReachValues[new Tuple<string, uint, uint>(v.Name, k + 1, i)]); // substitute to constant (needed for doing q.e.)
                    }
                    copy = (BoolExpr)copy.Substitute(idx, numidx); // must be outside variable loop

                    copy = Controller.Instance.Z3.MkAnd(copy, (BoolExpr)Controller.Instance.Sys.forallIdentity(Controller.Instance.Z3.MkInt(i), globalVariableResets, indexVariableResets, universalIndexVariableResets, this.UGuard, N));

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
                    }
                    transAll.Add(copy);
                }
                locInvariantAnd = Controller.Instance.Z3.MkOr(transAll.ToArray());
            }
            return locInvariantAnd;
        }
    }
}
