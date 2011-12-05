using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace phyea.model
{
    public abstract class AConcreteHybridAutomaton : AHybridAutomaton {

        public AConcreteHybridAutomaton(AHolism parent)
            : base(parent)
        {
        }
    }
}
