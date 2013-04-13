using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using passel.controller;

using Microsoft.Z3;

namespace passel.model
{
    public class ReachSymmetric
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

                /*
                foreach (var rs in ReachedStates)
                {
                    foreach (var s in ReachedStates)
                    {
                        if (s != rs && rs.Equals(s))
                        {
                            throw new Exception("Duplicate state reachable.");
                        }
                    }
                }

                foreach (var rs in ReachedStates)
                {
                    foreach (var s in Frontier)
                    {
                        if (rs.Equals(s))
                        {
                            throw new Exception("Added duplicate state.");
                        }
                    }
                }*/
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

                                    Expr post = Controller.Instance.Z3.copyExpr(tau.MakePost(symt.Formula));

                                    System.Console.WriteLine("NEXT TYPE: " + post);

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


                                        if (s.ContainsTypeFormula(post))
                                        {
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
                                                                    newTypes.Add(new SymmetricType(tmp.TN, tmp.Formula));
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
                                                                    newTypes.Add(new SymmetricType(tmp.TN, tmp.Formula));
                                                                }
                                                            }
                                                            newTypes.Add(symtnew);
                                                            newTypes.Add(nt);
                                                            //SymmetricType[] newTypes = s.Types.Except(new SymmetricType[] { symt } ).Union(new SymmetricType[] { symtnew, nt }).ToArray();
                                                            ns = new SymmetricState(N, newTypes.ToArray());
                                                        }

                                                        bool newState = true;
                                                        foreach (var checkrs in ReachedStates.Union(NewFrontier))
                                                        {
                                                            if (checkrs.Equals(ns))
                                                            {
                                                                newState = false;
                                                                break;
                                                            }
                                                        }
                                                        if (newState)
                                                        {
                                                            NewFrontier.Add(ns);
                                                        }
                                                    }
                                                }
                                                //}
                                            }
                                        }
                                        else
                                        {
                                            System.Console.WriteLine("NEW CASE");



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

                                            bool newState = true;
                                            foreach (var checkrs in ReachedStates.Union(NewFrontier))
                                            {
                                                if (checkrs.Equals(ns))
                                                {
                                                    newState = false;
                                                    break;
                                                }
                                            }
                                            if (newState)
                                            {
                                                NewFrontier.Add(ns);
                                            }
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

                                            bool newState = true;
                                            foreach (var checkrs in ReachedStates.Union(NewFrontier))
                                            {
                                                if (checkrs.Equals(ns))
                                                {
                                                    newState = false;
                                                    break;
                                                }
                                            }
                                            if (newState)
                                            {
                                                NewFrontier.Add(ns);
                                            }
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

    public static class SymHelp
    {
        /*
        public static IEnumerable<IEnumerable<T>> Combo<T>(this IEnumerable<T> elements, int k)
        {
            return k == 0 ? new[] { new T[0] } :
              elements.SelectMany((e, i) =>
                Combo(elements.Skip(i + 1), k - 1).Select(c => (new[] { e }).Concat(c)));
        }*/

        /*
        public static IEnumerable<IEnumerable<T>> Combinations<T>(this IEnumerable<T> elements, int k)
        {
            return k == 0 ? new[] { new T[0] } :
              elements.SelectMany((e, i) =>
                elements.Skip(i + 1).Combinations(k - 1).Select(c => (new[] { e }).Concat(c)));
        }*/


        public static List<List<uint>> TypePermutations(uint N, List<uint> TN)
        {
            List<List<uint>> perm = new List<List<uint>>();
            List<uint> ids = new List<uint>();
            Dictionary<uint, List<uint>> typeIds = new Dictionary<uint, List<uint>>();

            for (uint i = 1; i <= N; i++)
            {
                ids.Add(i);
            }

            for (uint t = 0; t < TN.Count; t++)
            {
                // idperms = permutations(ids, TN[t]) // gives back all permutations with TN[t] elements of ids
                //typeIds[t] = 

            }
            return perm;
        }


        public static IEnumerable<IEnumerable<T>> Permutations<T>(this IEnumerable<T> source)
        {
            if (source == null)
            {
                throw new ArgumentNullException("source");
            }
            // Ensure that the source IEnumerable is evaluated only once
            return PermutationsHelper(source.ToArray());
        }

        private static IEnumerable<IEnumerable<T>> PermutationsHelper<T>(IEnumerable<T> source)
        {
            var c = source.Count();
            if (c == 1)
            {
                yield return source;
            }
            else
            {
                for (int i = 0; i < c; i++)
                {
                    foreach (var p in PermutationsHelper(source.Take(i).Concat(source.Skip(i + 1))))
                    {
                        yield return source.Skip(i).Take(1).Concat(p);
                    }
                }
            }
        }
    }

    /// <summary>
    /// 
    /// </summary>
    public class SymmetricState
    {
        /// <summary>
        /// 
        /// </summary>
        public static HashSet<SymmetricState> AllStateTypes = new HashSet<SymmetricState>();


        /// <summary>
        /// Types composing this state
        /// </summary>
        public HashSet<SymmetricType> Types;

        /// <summary>
        /// Reachable symmetric states from this state (1-hop / edges)
        /// </summary>
        public HashSet<SymmetricState> Nexts;


        /// <summary>
        /// Check if two symmetric states have the same types, modulo the counts in the different types
        /// </summary>
        /// <param name="compare"></param>
        /// <returns></returns>
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

        public override bool Equals(object obj)
        {
            SymmetricState compare = (SymmetricState)obj;
            Boolean result = true;

            // can't be equal with unequal type length (short circuit)
            if (compare.Types.Count != this.Types.Count)
            {
                return false;
            }

            foreach (var ct in compare.Types)
            {
                Boolean maybe = false;
                foreach (var tt in this.Types)
                {
                    if ((ct.Formula == tt.Formula || Controller.Instance.Z3.ProveEqual(ct.Formula, tt.Formula)) && ct.TN == tt.TN)
                    {
                        maybe = true;
                        break; // short circuit
                    }
                }
                result = result && maybe;

                // short circuit
                if (!result)
                {
                    break;
                }
            }
            return result;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="type"></param>
        /// <returns></returns>
        public Boolean ContainsTypeFormula(SymmetricType type)
        {
            foreach (var t in this.Types)
            {
                if (t.Formula == type.Formula || Controller.Instance.Z3.ProveEqual(t.Formula, type.Formula))
                {
                    return true;
                }
            }
            return false;
        }

        public Boolean ContainsTypeFormula(Expr formula)
        {
            foreach (var t in this.Types)
            {
                if (t.Formula == formula || Controller.Instance.Z3.ProveEqual(t.Formula, formula))
                {
                    return true;
                }
            }
            return false;
        }

        public void MergeSameTypes(uint N)
        {
            foreach (var t in this.Types)
            {
                foreach (var s in this.Types)
                {
                    if (s == t)
                    {
                        continue;
                    }

                    if (t.Formula == s.Formula || Controller.Instance.Z3.ProveEqual(t.Formula, s.Formula))
                    {
                        t.TN += s.TN;
                        s.TN = 0;
                    }
                }
            }
            this.Types.RemoveWhere(v => v.TN == 0);
            this.CheckTypeSum(N);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="N"></param>
        /// <param name="types"></param>
        public SymmetricState(uint N, params SymmetricType[] types)
        {
            // copy input types
            this.Types = new HashSet<SymmetricType>();
            foreach (var t in types)
            {
                this.Types.Add(new SymmetricType(t.TN, t.Formula));
            }
            this.MergeSameTypes(N);
            if (!this.CheckTypeSum(N))
            {
                throw new Exception("ERROR: sum of type counts not equal to N");
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public override String ToString()
        {
            String s = "";
            foreach (SymmetricType t in Types)
            {
                s += "  " + t.ToString() + Environment.NewLine;
            }
            return s;
        }

        /*
        int level = -1;
        uint permutationCount = 0;
        Dictionary<uint, HashSet<uint>> idMap = new Dictionary<uint, HashSet<uint>>();
        Dictionary<uint, uint> idValues = new Dictionary<uint, uint>();

        public void visit(uint k, uint N)
        {
            if (level == -1)
            {
                for (uint i = 0; i < N; i++)
                {
                    idValues.Add(i, 0);
                }
            }
            level = level + 1;
            idValues[k] = (uint)level;
            if (level == N)
            {
                addPermutation(N);
            }
            else
            {
                for (uint i = 0; i < N; i++)
                {
                    if (idValues[i] == 0)
                    {
                        visit(i, N);
                    }
                }
            }
            level = level - 1;
            idValues[k] = 0;
        }

        void addPermutation(uint N)
        {
            HashSet<uint> ids = new HashSet<uint>();
            for (uint i = 0; i < N; i++)
            {
                ids.Add(idValues[i]);
            }
            idMap.Add(permutationCount, ids);
            permutationCount++;
        }
        */


        

        /*
        public static IEnumerable<uint> Combinations(List<uint> ids, int length)
        {
            for (int i = 0; i < ids.Count; i++)
            {
                // only want 1 character, just return this one
                if (length == 1)
                {
                    yield return ids[i];
                }

                // want more than one character, return this one plus all combinations one shorter
                // only use characters after the current one for the rest of the combinations
                else
                {
                    foreach (uint next in Combinations(ids.GetRange(i + 1, ids.Count - (i + 1)), length - 1))
                    {
                        yield return ids[i] + next;
                    }
                }
            }
        }*/


        /// <summary>
        ///  Generate equivalent concrete state (with actual identifier numbers instead of symbols)
        /// </summary>
        /// <returns></returns>
        public Expr ToConcrete()
        {
            BoolExpr concrete = Controller.Instance.Z3.MkTrue();

            // generate set of identifier permutations for each type
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
            }
            return concrete;
        }

        /// <summary>
        /// Check if all the Types corresponding to this ReachedState sum to the correct value of N
        /// </summary>
        /// <param name="N"></param>
        /// <returns></returns>
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

    /// <summary>
    /// 
    /// </summary>
    public class SymmetricType
    {
        /// <summary>
        /// 
        /// </summary>
        public uint TN;
        /// <summary>
        /// 
        /// </summary>
        public Expr Formula;
        /// <summary>
        /// 
        /// </summary>
        public static HashSet<Expr> AllTypes = new HashSet<Expr>();

        //public static EqualityComparer<SymmetricType> TypeFormulaComparer = new EqualityComparer<SymmetricType>();

        /// <summary>
        /// 
        /// </summary>
        /// <param name="TN"></param>
        /// <param name="Formula"></param>
        public SymmetricType(uint TN, Expr Formula)
        {
            AllTypes.Add(Formula); // todo: add formula -> typed state converter

            this.TN = TN;
            this.Formula = Formula;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public override String ToString()
        {
            return "<" + TN + ", " + Formula.ToString() + ">";
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="QuantifiedFormula"></param>
        /// <param name="N"></param>
        /*public SymmetricType(Expr QuantifiedFormula, uint N)
        {
            
        }*/
    }
}
