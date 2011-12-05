using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace phyea.model
{
    public class AAbstractHybridAutomaton : AHybridAutomaton
    {

        /**
         * States of the abstracted hybrid automaton
         */
        protected ISet<AAbstractState> _states = new HashSet<AAbstractState>();

        /**
         * Valuations of the abstracted hybrid automaton
         */
        protected ISet<AAbstractState> _valuations = new HashSet<AAbstractState>();

        /**
         * Default constructor
         */
        public AAbstractHybridAutomaton(AHolism parent)
            : base(parent)
        {
        }

        public ISet<AAbstractState> States
        {
            get { return this._states; }
            set { this._states = value; }
        }

        public ISet<AAbstractState> Valuations
        {
            get { return this._valuations; }
            set { this._valuations = value; }
        }
    }
}
