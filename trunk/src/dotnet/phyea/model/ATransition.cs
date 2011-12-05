using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;

namespace phyea.model
{
    public abstract class ATransition : ICloneable
    {
        public enum AbstractTransitionType { ref_ctrl, env_ctrl, ref_data, env_data, time };

        public Term Guard;
        protected Term _reset;
        protected List<AState> _nextStates;
        protected List<Term> _blockingSetRef;
        protected List<Term> _blockingSetEnvEC;
        protected List<Term> _blockingSetEnvCL;
        protected AbstractTransitionType _type;

        public ATransition()
        {
        }

        public ATransition(AState nextState)
        {
            this._nextStates = new List<AState>();
            this._nextStates.Add(nextState);
        }

        public ATransition(AState nextState, AbstractTransitionType t)
        {
            this._nextStates = new List<AState>();
            this._nextStates.Add(nextState);
            this._type = t;
        }

        public ATransition(List<AState> nextStates)
        {
            this._nextStates = nextStates;
        }

        public ATransition(Term guard, Term reset)
        {
            this.Guard = guard;
            this._reset = reset;
        }

        public ATransition(Term guard, Term reset, AState nextState)
        {
            this.Guard = guard;
            this._reset = reset;
            this._nextStates = new List<AState>();
            this._nextStates.Add(nextState);
        }

        public ATransition(Term guard, Term reset, List<AState> nextStates)
        {
            this.Guard = guard;
            this._reset = reset;
            this._nextStates = nextStates;
        }

        /*public Term Guard
        {
            get { return this._guard; }
            set { this._guard = value; }
        }*/

        public Term Reset
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
        public Term ToTerm()
        {
            List<Term> post = new List<Term>();
            foreach (AState l in this._nextStates)
            {
                post.Add(Controller.Instance.Z3.MkEq(Controller.Instance.QPrimed["i"], Controller.Instance.Z3.MkIntNumeral(l.Value)));
            }
            if (post.Count > 1)
            {
                return Controller.Instance.Z3.MkOr(post.ToArray());
            }
            else
            {
                return post.First(); // todo: catch if count == 0
            }
        }

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

        public List<Term> BlockingSetRef
        {
            get
            {
                if (this._blockingSetRef == null)
                {
                    this._blockingSetRef = new List<Term>();
                }
                return this._blockingSetRef;
            }
            set { this._blockingSetRef = value; }
        }

        public List<Term> BlockingSetEnvEC
        {
            get
            {
                if (this._blockingSetEnvEC == null)
                {
                    this._blockingSetEnvEC = new List<Term>();
                }
                return this._blockingSetEnvEC;
            }
            set { this._blockingSetEnvEC = value; }
        }

        public List<Term> BlockingSetEnvCL
        {
            get
            {
                if (this._blockingSetEnvCL == null)
                {
                    this._blockingSetEnvCL = new List<Term>();
                }
                return this._blockingSetEnvCL;
            }
            set { this._blockingSetEnvCL = value; }
        }

        public void addBlockingRef(Term b)
        {
            if (this._blockingSetRef == null)
            {
                this._blockingSetRef = new List<Term>();
            }
            // unique add
            if (!this._blockingSetRef.Contains(b))
            {
                this._blockingSetRef.Add(b);
            }
        }

        public void addBlockingEnvEC(Term b)
        {
            if (this._blockingSetEnvEC == null)
            {
                this._blockingSetEnvEC = new List<Term>();
            }
            // unique add
            if (!this._blockingSetEnvEC.Contains(b))
            {
                this._blockingSetEnvEC.Add(b);
            }
        }

        public void addBlockingEnvCL(Term b)
        {
            if (this._blockingSetEnvCL == null)
            {
                this._blockingSetEnvCL = new List<Term>();
            }
            // unique add
            if (!this._blockingSetEnvCL.Contains(b))
            {
                this._blockingSetEnvCL.Add(b);
            }
        }

        public abstract object Clone();
    }
}
