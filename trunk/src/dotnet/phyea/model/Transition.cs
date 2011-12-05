using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace phyea.model
{
    public class Transition : ATransition {

        public Transition()
            : base()
        {
        }

        public Transition(AState nextState)
            : base(nextState)
        {
        }

        public Transition(AState nextState, AbstractTransitionType t)
            : base(nextState, t)
        {
        }

        public Transition(List<AState> nextStates)
            : base(nextStates)
        {
        }

	    public Transition(Term guard, Term reset)
            : base(guard, reset)
        {
	    }

        public Transition(Term guard, Term reset, List<AState> nextStates)
            : base(guard, reset, nextStates)
        {
        }

        public Transition(Term guard, Term reset, AState nextState)
            : base(guard, reset, nextState)
        {
        }

        public override object Clone()
        {
            // deep copy the list
            //List<AState> newList = new List<AState>(this.NextStates.Count);
            //this.NextStates.ForEach((item) =>
            //{
            //    //newList.Add((AState)item.Clone());
            //    newList.Add((AState)item); // don't clone the next state...
            //});

            return new Transition(this.Guard, this.Reset, this.NextStates);
        }
    }
}
