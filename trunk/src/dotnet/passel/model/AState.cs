using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    /**
     * Control state of a (nondeterministic) finite state automaton
     */
    public abstract class AState : ICloneable
    {
        /**
         * Value for the state
         */
        protected UInt32 _value;

        public Expr ValueTerm;
        private Expr _statePredicate;

        public AHybridAutomaton Parent;


        public Expr LabelExpr;
        public Expr BitVectorExpr;

        /**
         * Name for the state
         */
        protected String _label;

        /**
         * True if this state is initial, false otherwise
         */
        protected Boolean _initial;

        /**
         * Transitions: edges to other states
         */
        private List<Transition> _transitions;

        public AState()
        {
        }

        public AState(AHybridAutomaton h, String label, UInt32 value, Boolean initial)
        {
            this.Parent = h;
            this._label = label;
            this._value = value;
            this._initial = initial;

            //this.ValueTerm = Controller.Instance.Z3.MkInt(value); // TODO: location type... Instance.LocType
            this.ValueTerm = Controller.Instance.Z3.MkConst(label, Controller.Instance.LocType);

            this.LabelExpr = this.ValueTerm;

            this.BitVectorExpr = Controller.Instance.Z3.MkBV(value, Controller.Instance.LocSize);

            //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkEq(this.ValueTerm, Controller.Instance.Z3.MkInt(value)));

            this._statePredicate = Controller.Instance.Z3.MkEq(Controller.Instance.IndexedVariables[new KeyValuePair<string,string>("q","i")], this.ValueTerm);

            // add label to value map
            if (label == "")
            {
                label = "mode" + value.ToString();
            }
            Controller.Instance.Locations.Add(label, this.ValueTerm);

            Controller.Instance.LocationNumTermToName.Add(this.ValueTerm, label);
        }

        public AState(AHybridAutomaton h, String label, UInt32 value, Boolean initial, List<Transition> transitions)
        {
            this.Parent = h;
            this._label = label;
            this._value = value;
            this._initial = initial;
            this._transitions = transitions;
        }

        public Boolean Initial
        {
            get { return this._initial; }
            set { this._initial = value; }
        }

        public override String ToString()
        {
            return this._label;
        }

        public Expr StatePredicate
        {
            get { return this._statePredicate; }
            set { this._statePredicate = value; }
        }

        public UInt32 Value
        {
            get { return this._value; }
            set { this._value = value; }
        }

        public String Label
        {
            get { return this._label; }
            set { this._label = value; }
        }

        public abstract object Clone();

        public List<Transition> Transitions
        {
            get
            {
                if (this._transitions == null)
                {
                    this._transitions = new List<Transition>();
                }
                return this._transitions;
            }
            set { this._transitions = value; }
        }


        /**
         * Determine if this state has a transition to at least one of the AStates in states
         */
        public Boolean containsTransitionToNext(List<AState> states)
        {
            foreach (Transition t in this._transitions)
            {
                foreach (AState s in states)
                {
                    if (t.NextStates.Contains(s))
                    {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Add a transition to this state
         */
        public void addTransition(Transition t)
        {
            if (this._transitions == null)
            {
                this._transitions = new List<Transition>();
            }

            // todo: removed this in next: might want to add back (but not from parsing, maybe in an automatic abstraction):   && !this.containsTransitionToNext(t.NextStates)
            if (!this._transitions.Contains(t))
            //if (!this._transitions.Contains(t) && !this.containsTransitionToNext(t.NextStates))
            {
                this._transitions.Add(t);
            }
        }
    }
}
