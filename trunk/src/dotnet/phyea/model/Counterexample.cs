using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace phyea.model
{
    public class Counterexample
    {
        public Model Model;
        public Term Claim;
        public ATransition Transition;

        public Counterexample(Model m)
        {
            this.Model = m;
        }

        public Counterexample(Model m, Term c)
        {
            this.Model = m;
            this.Claim = c;
        }

        public Counterexample(Model m, Term c, ATransition t)
        {
            this.Model = m;
            this.Claim = c;
            this.Transition = t;
        }
    }
}
