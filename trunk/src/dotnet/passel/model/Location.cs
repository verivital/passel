using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;
using passel.controller;

namespace passel.model
{
    /**
     * Location of a hybrid automaton
     */
    public class Location : AState
    {
        Expr _invariant;
        Expr _stop;
        List<Flow> _flows = new List<Flow>();


        // todo: use this later, for now let's just have a single flow term
        IDictionary<Variable, Expr> _varRates;

        public Location()
            : base()
        {
        }

        public Location(AHybridAutomaton h, String label, UInt32 value, Boolean initial)
            : base(h, label, value, initial)
        {

        }

        public Location(AHybridAutomaton h, String label, UInt32 value, Boolean initial, List<Transition> transitions)
            : base(h, label, value, initial, transitions)
        {

        }

        public Expr Invariant
        {
            get { return this._invariant; }
            set { this._invariant = value; }
        }

        public Expr Stop
        {
            get { return this._stop; }
            set { this._stop = value; }
        }

        public List<Flow> Flows
        {
            get { return this._flows; }
            set { this._flows = value; }
        }

        public IDictionary<Variable, Expr> VariableRates
        {
            get { return this._varRates; }
            set { this._varRates = value; }
        }

        public void setRateEqualForVar(Variable var, Expr rate)
        {
            if (this._varRates == null)
            {
                this._varRates = new Dictionary<Variable, Expr>();
            }

            // remove existing rate if already there
            if (this._varRates.ContainsKey(var))
            {
                this._varRates.Remove(var);
            }
            // add the newly specified rate
            this._varRates.Add(var, rate);
        }

        public override object Clone()
        {
            return null;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="t1"></param>
        /// <param name="t2"></param>
        /// <param name="delta"></param>
        /// <returns></returns>
        public List<BoolExpr> MakeFlow(Expr hidx, Expr t1, Expr t2, Expr delta)
        {
            List<BoolExpr> exprlist = new List<BoolExpr>();
            // add invariant
            if (this.Invariant != null)
            {
                Expr tmpterm = this.Invariant;

                // indexed variables
                foreach (var v in this.Parent.Variables)
                {
                    if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")], this, t1, t2, delta);
                    }
                    else
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")], this, t1, t2, null);
                        //tmpterm = z3.MkAnd(tmpterm, tmpterm.Substitute(
                    }
                }

                // TODO: NEED TO REASSIGNED tmpterm TO THE INVARIANT (AND STOPPING CONDITION IN THE NEXT ONE)?

                // global variables
                foreach (var v in this.Parent.Parent.Variables)
                {
                    if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.GlobalVariables[v.Name], this, t1, t2, delta);
                    }
                    else
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.GlobalVariables[v.Name], this, t1, t2, null);
                    }
                }

                // add invariant on primed vars
                Expr invCopy = Controller.Instance.Z3.copyExpr(this.Invariant);
                Controller.Instance.Z3.primeAllVariables(ref invCopy);
                tmpterm = Controller.Instance.Z3.MkAnd((BoolExpr)tmpterm, (BoolExpr)invCopy);

                exprlist.Add((BoolExpr)tmpterm);
            }

            // add stopping condition
            if (this.Stop != null)
            {
                Expr tmpterm = Controller.Instance.Z3.MkImplies((BoolExpr)this.Stop, Controller.Instance.Z3.MkEq(t1, t2));

                // indexed variables
                foreach (var v in this.Parent.Variables)
                {
                    if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")], this, t1, t2, delta);
                    }
                    else
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(v.Name, "i")], this, t1, t2, null);
                    }
                }

                // global variables
                foreach (var v in this.Parent.Parent.Variables)
                {
                    if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.GlobalVariables[v.Name], this, t1, t2, null);
                    }
                    else
                    {
                        tmpterm = this.Parent.Parent.makeFlowTransitionTerm(tmpterm, v, Controller.Instance.GlobalVariables[v.Name], this, t1, t2, null);
                    }
                }
                exprlist.Add((BoolExpr)tmpterm);
            }

            if (this.Flows == null || this.Flows.Count == 0 || this.Flows[0].DynamicsType == Flow.DynamicsTypes.constant) // TODO: CHECK ALL FLOWS, THIS WORKS ONLY FOR ONE VAR
            {
                Expr tmpterm = (BoolExpr)Controller.Instance.Sys.timeNoFlowIdentity(hidx);
                tmpterm = tmpterm.Substitute(Controller.Instance.Indices["i"], hidx); // replace i by h

                exprlist.Add((BoolExpr)tmpterm);

                //if (timeall.Count != h.Locations.Count) // only continue if nothing in timed list, otherwise if the last location has null flow, the others will also get skipped
                //{
                //    continue; // no dynamics (e.g., x' == 0), skip time transition
                //}
                // todo: this makes the most sense, but should we allow the full generality of having an invariant and stopping condition even when we will have identity for time? (i.e., the stop/inv could force a transition, but it would sort of be illegal...)
            }
            // do flow afterward, it already has primed variables
            else if (this.Flows != null)
            {
                foreach (Flow f in this.Flows)
                {
                    switch (f.DynamicsType)
                    {
                        case Flow.DynamicsTypes.constant:
                            {
                                exprlist.Add((BoolExpr)f.Value); // constant specifies equality: x[i] == x'[i]
                                break;
                            }
                        case Flow.DynamicsTypes.rectangular:
                            {
                                Expr flow = f.Value;
                                flow = f.Value.Args[0].Args[1]; // todo: generalize
                                if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                                {
                                    flow = flow.Substitute(f.RectRateA, delta); // replace A from \dot{x} \in [A,B] with \delta which exists in [A,B]
                                }

                                flow = Controller.Instance.Z3.MkEq(f.Value.Args[0].Args[0], flow);

                                if (Controller.Instance.FlowOption == Controller.FlowOptionType.relation)
                                {
                                    BoolExpr[] andTerms;
                                    andTerms = new BoolExpr[] { (BoolExpr)flow, Controller.Instance.Z3.MkGe((ArithExpr)delta, (ArithExpr)f.RectRateA), Controller.Instance.Z3.MkLe((ArithExpr)delta, (ArithExpr)f.RectRateB) }; // constrain: A <= delta <= B
                                    flow = Controller.Instance.Z3.MkAnd(andTerms);
                                }
                                else
                                {
                                    flow = f.Value; // TODO: refactor
                                    //andTerms = new BoolExpr[] { (BoolExpr)flow, z3.MkGe((ArithExpr)delta, (ArithExpr)f.RectRateA), z3.MkLe((ArithExpr)delta, (ArithExpr)f.RectRateB) }; // constrain: A <= delta <= B
                                }

                                exprlist.Add((BoolExpr)flow);
                                break;
                            }
                        case Flow.DynamicsTypes.timed:
                        default:
                            {
                                exprlist.Add((BoolExpr)f.Value);
                                break;
                            }
                    }
                }
            }
            return exprlist;
        }
    }
}
