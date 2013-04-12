using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using passel.controller;

using Microsoft.Z3;

namespace passel.model
{
    class ReachSymmetric
    {
        HashSet<SymmetricState> ReachedStates = new HashSet<SymmetricState>();

        public void ComputeReach(Holism sys, uint N)
        {
            AHybridAutomaton h = sys.HybridAutomata[0]; // todo: generalize for compositions

            HashSet<SymmetricState> Frontier = new HashSet<SymmetricState>();
            HashSet<SymmetricState> NewFrontier = new HashSet<SymmetricState>();

            SymmetricState init = new SymmetricState(N, new SymmetricType(N, h.makeInitialBmcSymmetric())); // todo: add formula -> typed state converter

            Frontier.Add(init);

            Controller.Instance.Z3.slvr.Push(); // push before adding assumptions
            Controller.Instance.Z3.slvr.Assert(Controller.Instance.Z3.Assumptions.ToArray()); // assert all the data-type assumptions
            Controller.Instance.Z3.slvr.Assert(Controller.Instance.Z3.AssumptionsUniversal.ToArray()); // assert all the data-type assumptions

            uint iterations = 0;

            while (Frontier.Count > 0)
            {
                System.Console.WriteLine("Symmetric BMC Iteration " + iterations);

                Console.WriteLine("Reached states so far:");
                foreach (var v in ReachedStates)
                {
                    Console.WriteLine(v);
                }

                ReachedStates.UnionWith(Frontier);

                NewFrontier = new HashSet<SymmetricState>();

                foreach (var s in Frontier)
                {
                    System.Console.WriteLine("Frontier state: " + Environment.NewLine);
                    System.Console.WriteLine(s.ToString());

                    foreach (SymmetricType symt in s.Types)
                    {
                    foreach (AState q in h.Locations)
                    {
                        foreach (Transition tau in q.Transitions)
                        {
                            
                                // skip immediately if no processes in this type
                                if (symt.TN == 0)
                                {
                                    continue;
                                }

                                // check if enabled
                                Expr tt = tau.makeTransitionTerm((ConcreteLocation)q, Controller.Instance.Indices["i"]);
                                Expr enabled = Controller.Instance.Z3.MkAnd((BoolExpr)symt.Formula, (BoolExpr)tt);
                                Model m;
                                Expr[] c;

                                if (Controller.Instance.Z3.checkTerm(enabled, out m, out c))
                                {
                                    System.Console.WriteLine("Enabled");




                                    //List<BoolExpr> newAssignments = new List<BoolExpr>();

                                    //Console.WriteLine("Variables: " + m.Eval(Controller.Instance.Indices["i"]));

                                    //Expr i_value = m.Eval(Controller.Instance.Indices["i"]);

                                    //newAssignments.Add(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(Controller.Instance.Indices["i"], i_value)));

                                    /*
                                    foreach (var vnew in h.Variables)
                                    {
                                        //Expr v = Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>(vnew.NamePrimed, "i")];
                                        Expr v = Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[vnew.Name], i_value);

                                        Console.WriteLine("Variables (" + vnew.Name + "): " + m.Eval(v));

                                        newAssignments.Add(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(v, m.Eval(v))));
                                    }

                                    foreach (var vnew in sys.Variables)
                                    {
                                        Expr v = Controller.Instance.GlobalVariablesPrimed[vnew.Name];

                                        Console.WriteLine("Variables (" + vnew.Name + "): " + m.Eval(v));

                                        //newAssignments.Add(Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(v, m.Eval(v))));
                                    }
                                    */

                                    //enabled = Controller.Instance.Z3.MkAnd((BoolExpr)enabled, Controller.Instance.Z3.MkAnd(newAssignments.ToArray()));

                                    /*
                                    Expr post = Controller.Instance.Z3.MkExists(new Expr[] { Controller.Instance.Indices["i"] }, (BoolExpr)enabled);
                                    Tactic tqe = Controller.Instance.Z3.MkTactic("snf");
                                    //tqe = Controller.Instance.Z3.Then(Controller.Instance.Z3.MkTactic("ctx-simplify"), Controller.Instance.Z3.MkTactic("snf"), tqe);
                                    Goal g = Controller.Instance.Z3.MkGoal();
                                    g.Assert((BoolExpr)post);
                                    ApplyResult ar = tqe.Apply(g);
                                    System.Console.WriteLine("POST: " + ar.ToString());
                                     */

                                    System.Console.WriteLine("NEXT TYPE: " + tau.MakePost());

                                    Expr post = Controller.Instance.Z3.copyExpr(tau.MakePost());
                                    Controller.Instance.Z3.unprimeAllVariables(ref post);



                                    //SymmetricState newState = new SymmetricState(N, s.Types, post);









                                    // created type before for some reachable state, find it
                                    if (SymmetricType.AllTypes.Contains(post))
                                    {
                                        System.Console.WriteLine("Existing type:" + post);

                                        // find state to increment and decrement
                                        /*
                                        foreach (var rs in ReachedStates)
                                        {
                                            // transition couldn't have been enabled
                                            if (!rs.Types.Contains(symt))
                                            {
                                                continue;
                                            }
                                         */

                                            foreach (var rstype in s.Types)
                                            {
                                                // just change counts of THIS state type
                                                if (post == rstype.Formula || Controller.Instance.Z3.ProveEqual((BoolExpr)post, (BoolExpr)rstype.Formula))
                                                {
                                                    // found matching type
                                                    System.Console.WriteLine("Found matching state and type: " + s);


                                                    SymmetricType nt = null;
                                                    SymmetricState ns = null;

                                                    // self loop
                                                    if (post == symt.Formula || Controller.Instance.Z3.ProveEqual((BoolExpr)post, (BoolExpr)symt.Formula))
                                                    {
                                                    }
                                                    else
                                                    {
                                                        nt = new SymmetricType(rstype.TN + 1, rstype.Formula); // todo: get right formula; todo: handle globals (may decrement all of old type to 0)
                                                        SymmetricType symtnew = new SymmetricType(symt.TN - 1, symt.Formula);

                                                        // remove if count is 0
                                                        if (symtnew.TN == 0)
                                                        {

                                                            HashSet<SymmetricType> newTypes = new HashSet<SymmetricType>();
                                                            foreach (var tmp in s.Types)
                                                            {
                                                                if (tmp.Formula == symt.Formula || tmp.Formula == nt.Formula || Controller.Instance.Z3.ProveEqual(symt.Formula, tmp.Formula) || Controller.Instance.Z3.ProveEqual(nt.Formula, tmp.Formula))
                                                                {
                                                                    continue;
                                                                }
                                                                else
                                                                {
                                                                    newTypes.Add(tmp);
                                                                }
                                                            }
                                                            newTypes.Add(nt);
                                                            //SymmetricType[] newTypes = s.Types.Except(new SymmetricType[] { symt } ).Union(new SymmetricType[] { symtnew, nt }).ToArray();
                                                            ns = new SymmetricState(N, newTypes.ToArray());
                                                            //ns = new SymmetricState(N, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { nt }).ToArray());
                                                        }
                                                        else
                                                        {
                                                            HashSet<SymmetricType> newTypes = new HashSet<SymmetricType>();
                                                            foreach (var tmp in s.Types)
                                                            {
                                                                if (tmp.Formula == symt.Formula || tmp.Formula == nt.Formula || Controller.Instance.Z3.ProveEqual(symt.Formula, tmp.Formula) || Controller.Instance.Z3.ProveEqual(nt.Formula, tmp.Formula))
                                                                {
                                                                    continue;
                                                                }
                                                                else
                                                                {
                                                                    newTypes.Add(tmp);
                                                                }
                                                            }
                                                            newTypes.Add(symtnew);
                                                            newTypes.Add(nt);
                                                            //SymmetricType[] newTypes = s.Types.Except(new SymmetricType[] { symt } ).Union(new SymmetricType[] { symtnew, nt }).ToArray();
                                                            ns = new SymmetricState(N, newTypes.ToArray());
                                                        }
                                                        NewFrontier.Add(ns);
                                                    }
                                                }
                                            //}
                                        }
                                    }
                                    else
                                    {
                                        bool newtype = true;

                                        foreach (var atype in SymmetricType.AllTypes)
                                        {
                                            Expr contains;
                                            contains = Controller.Instance.Z3.MkImplies((BoolExpr)post, (BoolExpr)symt.Formula);

                                            Model mtmp;
                                            Expr[] ctmp;
                                            String stmp;
                                            if (Controller.Instance.Z3.proveTerm(contains, out mtmp, out ctmp, out stmp))
                                            {
                                                // type exists, find it
                                                newtype = false;
                                                break;
                                            }
                                        }

                                        if (newtype)
                                        {
                                            // new type, create it
                                            //NewFrontier.Add(new SymmetricState(

                                            SymmetricType nt;
                                            SymmetricState ns = null;


                                            nt = new SymmetricType(1, post); // todo: get right formula; todo: handle globals (may decrement all of old type to 0)
                                            SymmetricType symtnew = new SymmetricType(symt.TN - 1, symt.Formula);
                                            // remove if count is 0
                                            if (symtnew.TN == 0)
                                            {
                                                ns = new SymmetricState(N, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { nt }).ToArray());
                                            }
                                            else
                                            {
                                                ns = new SymmetricState(N, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { symtnew, nt }).ToArray());
                                            }
                                            NewFrontier.Add(ns);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Frontier = NewFrontier;
                iterations++;
            }
            Controller.Instance.Z3.slvr.Pop(); // pop assumptions

            Console.WriteLine("Reachable states: ");
            foreach (var rs in ReachedStates)
            {
                Console.WriteLine(rs.ToString());
            }   
        }
    }

    class SymmetricState
    {
        /**
         * Types composing this state
         */
        public HashSet<SymmetricType> Types;

        /**
         * Reachable symmetric states from this state (1-hop / edges)
         */
        public HashSet<SymmetricState> Nexts;


        /**
         * Check if two symmetric states have the same types, modulo the counts in the different types
         */
        public Boolean SameTypes(SymmetricState compare)
        {
            Boolean result = true;
            foreach (var ct in compare.Types)
            {
                Boolean maybe = false;
                foreach (var tt in this.Types)
                {
                    if (ct.Formula == tt.Formula || Controller.Instance.Z3.ProveEqual(ct.Formula, tt.Formula))
                    {
                        maybe = true;
                    }
                }
                result = result && maybe;
            }
            return result;
        }

        public SymmetricState(uint N, params SymmetricType[] types)
        {
            Types = new HashSet<SymmetricType>(types);
            if (!this.CheckTypeSum(N))
            {
                throw new Exception("ERROR: sum of type counts not equal to N");
            }
        }

        public override String ToString()
        {
            String s = "";
            foreach (SymmetricType t in Types)
            {
                s += "  " + t.ToString() + Environment.NewLine;
            }
            return s;
        }

        /**
         * Generate equivalent concrete state (with actual identifier numbers instead of symbols)
         */
        public Expr ToConcrete()
        {
            BoolExpr concrete = Controller.Instance.Z3.MkTrue();
            foreach (SymmetricType st in Types)
            {
                HashSet<BoolExpr> cset = new HashSet<BoolExpr>();
                for (uint i = 1; i <= st.TN; i++)
                {
                    Expr ftmp = Controller.Instance.Z3.copyExpr(st.Formula); // deep copy
                    ftmp = ftmp.Substitute(Controller.Instance.Indices["i"], Controller.Instance.Z3.MkInt(i));
                    cset.Add((BoolExpr)ftmp);
                }
                concrete = Controller.Instance.Z3.MkAnd(cset.ToArray());
                // todo: conjunct with other types
            }
            return concrete;
        }

        /**
         * Check if all the Types corresponding to this ReachedState sum to the correct value of N
         */
        public Boolean CheckTypeSum(uint N)
        {
            uint sum = 0;
            foreach (var t in Types)
            {
                sum += t.TN;
            }

            if (sum != N)
            {
                if (sum > N)
                {
                    System.Console.WriteLine("WARNING: symmetric type N sum (" + sum + ") exceeds actual N (" + N + ").");
                }
                if (sum < N)
                {
                    System.Console.WriteLine("WARNING: symmetric type N sum (" + sum + ") less than actual N (" + N + ")");
                }
                return false;
            }
            else
            {
                return true;
            }
        }
    }

    class SymmetricType
    {
        public uint TN;
        public Expr Formula;

        public static HashSet<Expr> AllTypes = new HashSet<Expr>();

        //public static EqualityComparer<SymmetricType> TypeFormulaComparer = new EqualityComparer<SymmetricType>();

        public SymmetricType(uint TN, Expr Formula)
        {
            AllTypes.Add(Formula); // todo: add formula -> typed state converter

            this.TN = TN;
            this.Formula = Formula;
        }

        public override String ToString()
        {
            return "<" + TN + ", " + Formula.ToString() + ">";
        }

        /**
         * 
         */
        /*public SymmetricType(Expr QuantifiedFormula, uint N)
        {
            
        }*/
    }
}
