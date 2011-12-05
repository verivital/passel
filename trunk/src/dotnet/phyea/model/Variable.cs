using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace phyea.model
{
    public class Variable : AVariable
    {
        public Variable()
            : base()
        {
        }

        public Variable(String name, String rate, VarType type) 
            : base(name, rate, type)
        {
        }

    }
}
