using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;

namespace phyea.model
{
    /**
     * 
     */
    public abstract class ARate
    {
        public enum RateType { constant, nondeterministic, rectangular };

        private RateType _type;
        private Term[] _values;

        public ARate(RateType t, params Term[] values)
        {
            this._type = t;
            this._values = values;
        }

        public Term rateToConstraint(Term v)
        {
            switch (this._type)
            {
                case RateType.constant:
                    {
                        return Controller.Instance.Z3.MkEq(v, this._values[0]);
                    }
                case RateType.nondeterministic:
                    {
                        return Controller.Instance.Z3.MkEq(v, this._values[0]);
                    }
                case RateType.rectangular:
                    {
                        return Controller.Instance.Z3.MkEq(v, this._values[0]);
                    }
                default:
                    {
                        return Controller.Instance.Z3.MkEq(v, Controller.Instance.Z3.MkRealNumeral(0));
                    }
            }
        }
    }
}
