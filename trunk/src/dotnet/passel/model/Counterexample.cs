using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace passel.model
{
    public class Counterexample
    {
        public Model Model;
        public Expr Claim;
        public Transition Transition;

        public Counterexample(Model m)
        {
            this.Model = m;
        }

        public Counterexample(Model m, Expr c)
        {
            this.Model = m;
            this.Claim = c;
        }

        public Counterexample(Model m, Expr c, Transition t)
        {
            this.Model = m;
            this.Claim = c;
            this.Transition = t;
        }
    }
}
