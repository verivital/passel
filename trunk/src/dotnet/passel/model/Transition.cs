using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    public class Transition : ICloneable
    {
        public enum AbstractTransitionType { ref_ctrl, env_ctrl, ref_data, env_data, time };

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
                this.TransitionTermGlobal = (BoolExpr)Controller.Instance.Sys.makeTransitionTerm(this, null, hidxinner, null); // no local vars
                this.TransitionTerm = (BoolExpr)Controller.Instance.Sys.makeTransitionTerm(this, value, hidxinner, null); // with local vars
            }
        }

        public BoolExpr TransitionTermGlobal;

        public Transition(ConcreteLocation p)
        {
            this.Parent = p;

            // todo next: switch if not int type: , Controller.Instance.IndexType
            Expr hidxinner = Controller.Instance.Z3.MkIntConst("h");
            this.TransitionTermGlobal = (BoolExpr)Controller.Instance.Sys.makeTransitionTerm(this, null, hidxinner, null); // no local vars
            this.TransitionTerm = (BoolExpr)Controller.Instance.Sys.makeTransitionTerm(this, this.Parent, hidxinner, null); // with local vars
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

        public object Clone()
        {
            // deep copy the list
            //List<AState> newList = new List<AState>(this.NextStates.Count);
            //this.NextStates.ForEach((item) =>
            //{
            //    //newList.Add((AState)item.Clone());
            //    newList.Add((AState)item); // don't clone the next state...
            //});

            //return new Transition(this.Guard, this.Reset, this.NextStates);
            return null;
        }
    }
}
