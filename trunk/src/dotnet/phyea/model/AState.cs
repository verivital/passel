using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace phyea.model
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
        private List<ATransition> _transitions;

        public AState()
        {
        }

        public AState(String label, UInt32 value, Boolean initial)
        {
            this._label = label;
            this._value = value;
            this._initial = initial;
        }

        public AState(String label, UInt32 value, Boolean initial, List<ATransition> transitions)
        {
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

        public List<ATransition> Transitions
        {
            get
            {
                if (this._transitions == null)
                {
                    this._transitions = new List<ATransition>();
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
            foreach (ATransition t in this._transitions)
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
        public void addTransition(ATransition t)
        {
            if (this._transitions == null)
            {
                this._transitions = new List<ATransition>();
            }
            
            if (!this._transitions.Contains(t) && !this.containsTransitionToNext(t.NextStates))
            {
                this._transitions.Add(t);
            }
        }
    }
}
