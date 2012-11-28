using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    /**
     * 
     */
    public class Flow
    {
        public DynamicsTypes DynamicsType;
        public Variable Variable; // pointer to variable for this flow

        public enum DynamicsTypes
        {
            constant, // \dot{x} = 0
            timed,
            rectangular,
            linear,
            affine,
            nonlinear,
        }

        public Expr Value;

        public Flow()
        {
        }

        public Flow(DynamicsTypes t, Expr flow, Variable v)
        {
            this.DynamicsType = t;
            this.Value = flow;
            this.Variable = v;
        }

        public Expr RectRateA;
        public Expr RectRateB;

        public override String ToString()
        {
            string r = "\\dot{" + Variable.Name + "} = ";
            switch (DynamicsType)
            {
                case DynamicsTypes.constant:
                    r += "0";
                    break;
                case DynamicsTypes.timed:
                    r += RectRateA;
                    break;
                case DynamicsTypes.rectangular:
                    r += "\\in [" + RectRateA + ", " + RectRateB + "]";
                    break;
                case DynamicsTypes.nonlinear:
                default:
                    r += "f(" + Variable.Name + ")";
                    break;
            }
            return r;
        }
    }
}
