using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using passel.controller;

using Microsoft.Z3;
using System.Data;

using QuickGraph;

//using System.gra

namespace passel.model
{
    /// <summary>
    /// 
    /// </summary>
    public static class ReachSymmetric
    {
        /// <summary>
        /// 
        /// </summary>
        public static HashSet<SymmetricState> ReachedStates = new HashSet<SymmetricState>();

        /// <summary>
        /// 
        /// </summary>
        public static AdjacencyGraph<SymmetricState, TaggedEdge<SymmetricState, Transition>> ReachGraph = new AdjacencyGraph<SymmetricState, TaggedEdge<SymmetricState, Transition>>();

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sys"></param>
        /// <param name="N"></param>
        public static Dictionary<IEdge<SymmetricState>, Transition> ReachGraphTransitions = new Dictionary<IEdge<SymmetricState>, Transition>();

        /// <summary>
        /// Add a "weighted" edge to the graph (where weight is the transition)
        /// </summary>
        /// <param name="source"></param>
        /// <param name="target"></param>
        /// <param name="tau"></param>
        public static void AddEdgeWithTransition(SymmetricState source, SymmetricState target, Transition tau)
        {
            var edge = new TaggedEdge<SymmetricState,Transition>(source, target, tau);
            ReachGraph.AddVertex(source);
            ReachGraph.AddVertex(target);
            ReachGraph.AddEdge(edge);
            ReachGraphTransitions.Add(edge, tau);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sys"></param>
        /// <param name="N"></param>
        public static void ComputeReach(Holism sys, uint N)
        {
            AHybridAutomaton h = sys.HybridAutomata[0]; // todo: generalize for compositions

            HashSet<SymmetricState> Frontier = new HashSet<SymmetricState>();
            HashSet<SymmetricState> NewFrontier = new HashSet<SymmetricState>();

            SymmetricState init = new SymmetricState(N, true, new SymmetricType(N, h.makeInitialBmcSymmetric())); // todo: add formula -> typed state converter

            Frontier.Add(init);

            Controller.Instance.Z3.slvr.Push(); // push before adding assumptions
            Controller.Instance.Z3.slvr.Assert(Controller.Instance.Z3.Assumptions.ToArray()); // assert all the data-type assumptions
            Controller.Instance.Z3.slvr.Assert(Controller.Instance.Z3.AssumptionsUniversal.ToArray()); // assert all the data-type assumptions

            Console.WriteLine("Assumptions: ");
            Console.WriteLine(Controller.Instance.Z3.ExprArrayToString(Controller.Instance.Z3.Assumptions.ToArray()));
            Console.WriteLine(Controller.Instance.Z3.ExprArrayToString(Controller.Instance.Z3.AssumptionsUniversal.ToArray()));

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


                    // only try time post if system has continuous variables
                    if (h.Variables.Any(v => v.UpdateType == Variable.VarUpdateType.continuous) && s.Types.Any(ts => ts.CreatedHow != SymmetricType.CreationType.Continuous))
                    {
                        // only perform time post if time can flow from this state
                        if (s.IsTimeEnabled(N))
                        {
                            System.Console.WriteLine("TIME IS ENABLED");

                            HashSet<SymmetricState> newStates = s.MakeTimePost(N);
                            foreach (SymmetricState newState in newStates)
                            {
                                if (newState.IsNew() && !s.Equals(newState))
                                {
                                    NewFrontier.Add(newState);
                                    newState.SetNotNew();
                                }
                            }
                        }
                    }



                    foreach (SymmetricType symt in s.Types)
                    {
                        // skip immediately if no processes in this type
                        if (symt.TN == 0)
                        {
                            throw new Exception("Type with no processes...");
                            continue;
                        }

                        foreach (AState q in h.Locations)
                        {
                            foreach (Transition tau in q.Transitions)
                            {
                                if (tau.IsEnabled(symt.Formula))
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

                                    Expr post = tau.MakePost(symt.Formula);

                                    System.Console.WriteLine("NEXT TYPE: " + post);

                                    // created type before for some reachable state, find it
                                    if (SymmetricType.ExistingType(post))
                                    {
                                        System.Console.WriteLine("Existing type:" + post);

                                        /*if (s.ContainsTypeFormula(post))
                                        {
                                            foreach (var rstype in s.Types)
                                            {
                                                // just change counts of THIS state type
                                                if (post == rstype.Formula || Controller.Instance.Z3.ProveEqual((BoolExpr)post, (BoolExpr)rstype.Formula))
                                                {
                                                    // found matching type
                                                    System.Console.WriteLine("Found matching state and type: " + s);
                                                    SymmetricType nt;
                                                    SymmetricState ns;

                                                    // self loop
                                                    // todo: if self-loop changes variables, have to compute post
                                                    if (!(post == symt.Formula || Controller.Instance.Z3.ProveEqual((BoolExpr)post, (BoolExpr)symt.Formula)))
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
                                        {*/
                                            System.Console.WriteLine("NEW CASE");

                                            SymmetricType nt;
                                            SymmetricState ns;

                                        // REFACTOR_START
                                            nt = new SymmetricType(1, post); // todo: get right formula; todo: handle globals (may decrement all of old type to 0)

                                            if (tau.HasGlobalReset())
                                            {
                                                HashSet<SymmetricType> newTypes = makeTypesWithGlobalReset(s, symt, post);
                                                // 2: set globals to values in new type
                                                //   a: project away non-globals in new type
                                                //   b: conjunct with each type

                                                ns = new SymmetricState(N, s, tau, newTypes.Union( new SymmetricType[] { nt }).ToArray());
                                                // REFACTOR_END
                                            }
                                            else
                                            {
                                                SymmetricType symtnew = new SymmetricType(symt.TN - 1, symt.Formula);
                                                // remove if count is 0
                                                if (symtnew.TN == 0)
                                                {
                                                    ns = new SymmetricState(N, s, tau, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { nt }).ToArray());
                                                }
                                                else
                                                {
                                                    ns = new SymmetricState(N, s, tau, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { symtnew, nt }).ToArray());
                                                }
                                            }

                                            if (ns.IsNew())
                                            {
                                                NewFrontier.Add(ns);
                                                ns.SetNotNew();
                                            }
                                        //}
                                    }
                                    else
                                    {
                                        // new type, create it
                                        SymmetricType nt;
                                        SymmetricState ns = null;

                                        // REFACTOR_START
                                        nt = new SymmetricType(1, post); // todo: get right formula; todo: handle globals (may decrement all of old type to 0)

                                        if (tau.HasGlobalReset())
                                        {
                                            HashSet<SymmetricType> newTypes = makeTypesWithGlobalReset(s, symt, post);

                                            // 2: set globals to values in new type
                                            //   a: project away non-globals in new type
                                            //   b: conjunct with each type
                                            ns = new SymmetricState(N, s, tau, newTypes.Union(new SymmetricType[] { nt }).ToArray());
                                        }
                                        // REFACTOR_END
                                        else
                                        {
                                            SymmetricType symtnew = new SymmetricType(symt.TN - 1, symt.Formula);
                                            // remove if count is 0
                                            if (symtnew.TN == 0)
                                            {
                                                ns = new SymmetricState(N, s, tau, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { nt }).ToArray());
                                            }
                                            else
                                            {
                                                ns = new SymmetricState(N, s, tau, s.Types.Except(new SymmetricType[] { symt }).Union(new SymmetricType[] { symtnew, nt }).ToArray());
                                            }
                                        }

                                        // has to be new
                                        NewFrontier.Add(ns);
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

        private static HashSet<SymmetricType> makeTypesWithGlobalReset(SymmetricState oldState, SymmetricType oldType, Expr post)
        {
            HashSet<SymmetricType> newTypes = new HashSet<SymmetricType>();
            // 1: project away globals of existing type
            foreach (var ptype in oldState.Types)
            {
                Expr f = fixGlobals(ptype.Formula, post);
                SymmetricType ntmp = new SymmetricType(ptype.TN, f);

                if (ptype.Formula == oldType.Formula)
                {
                    ntmp.TN -= 1;
                }

                newTypes.Add(ntmp);
            }
            return newTypes;
        }

        private static Expr fixGlobals(Expr origFormula, Expr postFormula)
        {
            Expr globalReset = Controller.Instance.Z3.projectAwayIndexVariables(postFormula);
            Expr f = Controller.Instance.Z3.projectAwayGlobals(origFormula); // remove all globals, we'll add them back

            // global index abstraction
            if (Controller.Instance.Sys.Variables.Any(v => v.Type == Variable.VarType.index) && globalReset.ToString().Contains(" i"))
            {
                // todo next: generalize
                f = Controller.Instance.Z3.MkAnd((BoolExpr)f, Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkNot((BoolExpr)globalReset), Controller.Instance.Z3.MkNot((BoolExpr)Controller.Instance.Sys.Variables[0].Initially)));
            }
            else
            {
                f = Controller.Instance.Z3.MkAnd((BoolExpr)f, (BoolExpr)globalReset);
            }

            return f;
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

        private Boolean _new = true;

        public Boolean Initial = false;
        public Boolean CreatedByTime = false;
        public Transition CreatedBy;

        public SymmetricState PreState = null;

        /// <summary>
        /// Returns true if some positive (real) amount of time can elapse
        /// </summary>
        public Boolean IsTimeEnabled(uint N)
        {
            Boolean result = true;

            //foreach (var loc in Controller.Instance.Sys.HybridAutomata[0].Locations)
            //{
            //}

            //foreach (var t in this.Types)
            //{
                // TODO: this is never disabled... use the type flow constraint created for the actual time post rather than this
                //Expr enabled = Controller.Instance.Sys.makeFlowsAll(Controller.Instance.Sys.HybridAutomata[0], t.Formula);

                Expr enabled = this.MakeTimePostFormula(N, false);

                bool tmpstop = this.ToString().Trim().Contains("<2, (and (= (q i) idle) (= g 1) (not (<= (x i) 0.0)) (<= (x i) 5.0))>");

            if (tmpstop)
            {
                tmpstop = false;

                Expr enabledfake = this.MakeTimePostFormula(N, false);
            }

                System.Console.WriteLine("Time enabled query?: " + enabled.ToString());
                Model m;
                if (!Controller.Instance.Z3.checkTerm(enabled, out m))
                {
                    result = false;
                    //break;
                }
                else
                {
                    System.Console.WriteLine("Time enabled model: " + m.ToString());
                }
            //}
            return result;
        }

        private static Dictionary<SymmetricType, Location> CacheTypeLocations = new Dictionary<SymmetricType, Location>();

        private Dictionary<SymmetricType, String> typesToIds = new Dictionary<SymmetricType, string>();
        private Dictionary<Tuple<Variable, String>, Expr> gvToExpr = new Dictionary<Tuple<Variable, string>, Expr>();
        private Dictionary<Tuple<Variable, String>, Expr> gvToExprPost = new Dictionary<Tuple<Variable, string>, Expr>();


        /// <summary>
        /// Create formula for time post
        /// </summary>
        /// <param name="N"></param>
        /// <returns></returns>
        public Expr MakeTimePostFormula(uint N, bool allExists = false)
        {
            uint ti = 0;
            List<BoolExpr> timePostList = new List<BoolExpr>();


            // initialize shared var
            this.typesToIds = new Dictionary<SymmetricType, string>();
            this.gvToExpr = new Dictionary<Tuple<Variable, string>, Expr>();
            this.gvToExprPost = new Dictionary<Tuple<Variable, string>, Expr>();

            List<Expr> bound = new List<Expr>();




            

            string idxName = "i";


            Expr t1 = Controller.Instance.Z3.MkRealConst("t_1");
            Expr t2 = Controller.Instance.Z3.MkRealConst("t_2");
            Expr delta = Controller.Instance.Z3.MkRealConst("delta");

            bound.Add(t1);


            foreach (var loc in Controller.Instance.Sys.HybridAutomata[0].Locations)
            {
                foreach (var t in this.Types)
                {
                    Expr formula = Controller.Instance.Z3.copyExpr(t.Formula); // deep copy

                    /*
                    if (CacheTypeLocations.ContainsKey(t))
                    {
                        // do post
                    }
                    else*/
                    if (!Controller.Instance.Z3.ProveContains(loc.StatePredicate, formula))
                    {
                        /*CacheTypeLocations.Add(t, loc);
                    }
                    else
                    {*/
                        // skip
                        continue;
                    }

                    // compute post using dynamics for Location loc from pre-state formula t.Formula
                    Expr idx = Controller.Instance.Indices[idxName];


                    List<BoolExpr> dynamicsList = loc.MakeFlow(Controller.Instance.Indices["i"], t1, t2, delta);

                    // pre-state
                    dynamicsList.Add((BoolExpr)formula);

                    // identity
                    dynamicsList.Add((BoolExpr)Controller.Instance.Sys.timeIdentity(Controller.Instance.Indices["i"]));

                    dynamicsList.Add(Controller.Instance.Z3.MkGt((ArithExpr)t1, (ArithExpr)Controller.Instance.Z3.MkReal(0)));

                    BoolExpr dynamics;
                    if (dynamicsList.Count > 1)
                    {
                        dynamics = Controller.Instance.Z3.MkAnd(dynamicsList.ToArray());
                    }
                    else if (dynamicsList.Count == 1)
                    {
                        dynamics = dynamicsList[0];
                    }
                    else
                    {
                        throw new Exception("ERROR: time post failure.");
                    }

                    //bound.Add(t1);

                    Expr post = dynamics;

                    foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
                    {
                        //TODO: replace by type number -> unique id
                        Expr varConst = Controller.Instance.Z3.MkConst(v.Name + "_" + idxName, v.TypeSort);
                        Expr varConstPost = Controller.Instance.Z3.MkConst(v.NamePrimed + "_" + idxName, v.TypeSort);
                        post = post.Substitute(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Indices["i"]), varConst); // all in terms of i at this point
                        post = post.Substitute(Controller.Instance.Z3.MkApp(v.ValuePrimed, Controller.Instance.Indices["i"]), varConstPost);

                        if (allExists)
                        {
                            bound.Add(varConst);
                        }
                    }



                    // TODO: rename globals to e.g., g --> gi for type i, g --> gj for type j?
                    //       While the values will be consistent without doing this, we don't know how to recapture the values to the appropriate types otherwise if we separate them back out...
                    // TODO: only need to do this for states with > 1 type (possible performance improvement, but more complex)
                    foreach (var v in Controller.Instance.Sys.Variables)
                    {
                        Expr gtmp = Controller.Instance.Z3.MkConst(v.Name + "_" + idxName, Controller.Instance.GlobalVariables[v.Name].Sort);
                        Expr gtmpPost = Controller.Instance.Z3.MkConst(v.Name + "_" + idxName + Controller.PRIME_SUFFIX, Controller.Instance.GlobalVariables[v.Name].Sort);

                        gvToExpr.Add(new Tuple<Variable, string>(v, idxName), gtmp);
                        gvToExprPost.Add(new Tuple<Variable, string>(v, idxName), gtmpPost);

                        post = post.Substitute(Controller.Instance.GlobalVariables[v.Name], gtmp);
                        post = post.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Name], gtmpPost);
                    }











                    //post = Controller.Instance.Z3.MkForall(new[] { t2 }, (BoolExpr)post);
                    //post = Controller.Instance.Z3.MkExists(new[] { t2 }, (BoolExpr)post);
                    post = post.Substitute(delta, Controller.Instance.Z3.MkReal(1)); // TODO: only timed for now
                    post = post.Substitute(t2, t1); // TODO: only timed for now
                    //post = Controller.Instance.Z3.MkExists(new[] { delta }, (BoolExpr)post);
                    //post = Controller.Instance.Z3.MkExists(new[] { t1 }, (BoolExpr)post);
                    //bound.Add(t1);
                    //post = Controller.Instance.Z3.MkExists(bound.ToArray(), post);

                    timePostList.Add((BoolExpr)post);

                    // TODO NEXT: assumes at most 1 location per type (prove this invariant)

                    //if (!typesToIds.ContainsKey(t))
                    //{
                    this.typesToIds.Add(t, idxName);
                    //}

                    idxName = ((char)((idxName[0] + (char)0x01))).ToString();
                }

            }


            if (allExists)
            {
                foreach (var v in Controller.Instance.Sys.Variables)
                {
                    //bound.Add(Controller.Instance.GlobalVariables[v.Name]);
                    foreach (var t in this.Types)
                    {
                        bound.Add(gvToExpr[new Tuple<Variable, string>(v, typesToIds[t])]);
                    }
                }
            }

            BoolExpr timePost;
            if (timePostList.Count == 1)
            {
                timePost = timePostList[0];
            }
            else if (timePostList.Count >= 1)
            {
                timePost = Controller.Instance.Z3.MkAnd(timePostList.ToArray());

            }
            else
            {
                throw new Exception("ERROR: time post failure, no expressions.");
            }

            timePost = Controller.Instance.Z3.MkExists(bound.ToArray(), timePost);
            return timePost;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="N"></param>
        /// <returns></returns>
        public HashSet<SymmetricState> MakeTimePost(uint N)
        {
            HashSet<SymmetricState> newStates = new HashSet<SymmetricState>();

            // time-post closure: time_post(time_post(X)) = time_post(X)
            // TODO: prove
            if (this.Types.All(t => t.CreatedHow == SymmetricType.CreationType.Continuous))
            {
                newStates.Add(this);
                return newStates;
            }

            Expr timePost = this.MakeTimePostFormula(N, true);
            

            Tactic tqe = Controller.Instance.Z3.Repeat(Controller.Instance.Z3.Then(Controller.Instance.Z3.MkTactic("ctx-simplify"), Controller.Instance.Z3.MkTactic("qe")));
            //Tactic tqe = Controller.Instance.Z3.MkTactic("qe");

            Params p = Controller.Instance.Z3.MkParams();
            p.Add("qe-nonlinear", true);
            p.Add("eliminate-variables-as-block", true);
            tqe = Controller.Instance.Z3.With(tqe, p);

            Goal g = Controller.Instance.Z3.MkGoal();
            g = g.Translate(Controller.Instance.Z3);
            g.Assert((BoolExpr)timePost);

            List<BoolExpr> remAss = Controller.Instance.Z3.Assumptions.FindAll(a => a.IsQuantifier); // todo: add type constraints to constant (q_i) instead of functions (q i)
            Controller.Instance.Z3.Assumptions.RemoveAll(a => a.IsQuantifier); // otherwise q.e. will fail
            g.Assert(Controller.Instance.Z3.Assumptions.ToArray());
            Controller.Instance.Z3.Assumptions.AddRange(remAss); // add back
            g.Assert(Controller.Instance.Z3.AssumptionsUniversal.ToArray());
            g = g.Simplify();

            ApplyResult ar = tqe.Apply(g);

            List<BoolExpr> postStates = new List<BoolExpr>();
            foreach (var sg in ar.Subgoals)
            {
                postStates.AddRange(sg.Formulas);
            }

            postStates.RemoveAll(f => Controller.Instance.Z3.Assumptions.Contains(f));
            postStates.RemoveAll(f => Controller.Instance.Z3.AssumptionsUniversal.Contains(f));
            Controller.Instance.Z3.AssumptionsUniversal.ForEach(f => f.Simplify());
            postStates.RemoveAll(f => Controller.Instance.Z3.AssumptionsUniversal.Contains(f));
            //postStates.RemoveAll(f => Controller.Instance.Z3.

            Expr postStateOrig = Controller.Instance.Z3.MkAnd(postStates.ToArray());
            postStateOrig = postStateOrig.Simplify();

            postStateOrig = Controller.Instance.simplifyFormula(postStateOrig);

            // TODO: stronger simplify

            HashSet<Expr> postStatesFixed;

            if (postStateOrig.IsOr)
            {
                // split disjunct into several classes
                postStatesFixed = new HashSet<Expr>(postStateOrig.Args);

                //throw new Exception("Make multiple types");
            }
            else
            {
                postStatesFixed = new HashSet<Expr>(new Expr[] { postStateOrig } );
            }

            foreach (Expr postStateIter in postStatesFixed)
            {
                HashSet<SymmetricType> newTypes = new HashSet<SymmetricType>();
                Expr postState = postStateIter.Simplify();


                // TODO: at this point, before converting constants back to functions, re-create types
                // steps
                // 1. for each type, project away other variables, including type-specific globals (gi, gj, etc): exists (varnames != varname(type)) . formula
                // 2. perform next constant -> function steps for all these new types (do it with the types instead of formulas in case we need more info like # processes later)

                // potential todo later: associate a number with each var in each type (if we allow more than one, tbd)

                foreach (var t in this.Types)
                {
                    Expr postStateFixed = Controller.Instance.Z3.copyExpr(postState);
                    List<Expr> projectAway = new List<Expr>();
                    foreach (var ot in this.Types)
                    {
                        if (t == ot)
                        {
                            continue;
                        }
                        //typesToIds[t];
                        //typesToIds[ot];

                        foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
                        {
                            //projectAway.Add(Controller.Instance.Z3.MkConst( v.Name + "_" + typesToIds[ot], v.TypeSort ));
                            projectAway.Add(Controller.Instance.Z3.MkConst(v.Name + Controller.PRIME_SUFFIX + "_" + typesToIds[ot], v.TypeSort));
                        }

                        foreach (var v in Controller.Instance.Sys.Variables)
                        {
                            //projectAway.Add(Controller.Instance.Z3.MkConst(v.Name + "_" + typesToIds[ot], v.TypeSort));
                            projectAway.Add(Controller.Instance.Z3.MkConst(v.Name + "_" + typesToIds[ot] + Controller.PRIME_SUFFIX, v.TypeSort));
                        }
                    }

                    // do the projection, create the type
                    Expr newTypeFormula = Controller.Instance.Z3.projectAway(postStateFixed, projectAway);
                    SymmetricType newType = new SymmetricType(t.TN, newTypeFormula); // copy old type count
                    typesToIds.Add(newType, typesToIds[t]);
                    newTypes.Add(newType);
                }

                // convert constants back to functions
                foreach (var t in newTypes)
                {
                    Expr idxBound = Controller.Instance.Indices[typesToIds[t]];

                    foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
                    {
                        Expr varConst = Controller.Instance.Z3.MkConst(v.Name + "_" + typesToIds[t], v.TypeSort);
                        Expr varConstPost = Controller.Instance.Z3.MkConst(v.NamePrimed + "_" + typesToIds[t], v.TypeSort);
                        t.Formula = t.Formula.Substitute(varConst, Controller.Instance.Z3.MkApp(v.Value, idxBound));
                        t.Formula = t.Formula.Substitute(varConstPost, Controller.Instance.Z3.MkApp(v.ValuePrimed, idxBound));
                    }
                }

                // convert globals back
                foreach (var v in Controller.Instance.Sys.Variables)
                {
                    //bound.Add(Controller.Instance.GlobalVariables[v.Name]);
                    foreach (var t in newTypes)
                    {
                        t.Formula = t.Formula.Substitute(gvToExpr[new Tuple<Variable, string>(v, typesToIds[t])], Controller.Instance.GlobalVariables[v.Name]);
                        t.Formula = t.Formula.Substitute(gvToExprPost[new Tuple<Variable, string>(v, typesToIds[t])], Controller.Instance.GlobalVariablesPrimed[v.Name]);
                    }
                }

                foreach (var t in newTypes)
                {
                    Expr postStateFinal = Controller.Instance.Z3.copyExpr(t.Formula);
                    Controller.Instance.Z3.unprimeAllVariables(ref postStateFinal); // unprime
                    t.Formula = postStateFinal;
                }


                // convert names back
                foreach (var t in newTypes)
                {
                    if (typesToIds[t] != "i")
                    {
                        t.Formula = t.Formula.Substitute(Controller.Instance.Indices[typesToIds[t]], Controller.Instance.Indices["i"]);
                    }

                    // set continuuos creation type
                    t.CreatedHow = SymmetricType.CreationType.Continuous;
                }

                //newTypes.Add(new SymmetricType(N, postStateFinal));

                // TODO: add time "transitions" for every location that has a non-trivial (0 ode) flow
                SymmetricState newState = new SymmetricState(N, this, Transition.TimeTransition, newTypes.ToArray());
                newState.CreatedByTime = true;
                newStates.Add(newState);
            }
            return newStates;
        }

        /// <summary>
        /// Return true if this state is new
        /// </summary>
        /// <returns></returns>
        public Boolean IsNew()
        {
            return this._new;
        }

        public void SetNotNew()
        {
            this._new = false;
        }

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
                    //if (ct.Formula == tt.Formula || Controller.Instance.Z3.CheckEqual(ct.Formula, tt.Formula)) // needs to be prove
                    if (ct.Formula == tt.Formula || Controller.Instance.Z3.ProveEqual(ct.Formula, tt.Formula))
                    {
                        maybe = true;
                    }
                }
                result = result && maybe;
            }
            return result;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="obj"></param>
        /// <returns></returns>
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
                    // TODO: add option to toggle this, OR BETTER YET, set up another cache to map all equal formulas
                    //          DICTIONARY from EXPR to EXPR: given an EXPR, if it is in dictionary, returns expression it has been proven equal to (will save lots of sat checks)
                    if (ct.TN == tt.TN && (ct.Formula == tt.Formula || Controller.Instance.Z3.ProveContains(tt.Formula, ct.Formula)))
                    //if (ct.TN == tt.TN && (ct.Formula == tt.Formula || Controller.Instance.Z3.ProveEqual(ct.Formula, tt.Formula)))
                    //if (ct.TN == tt.TN && (ct.Formula == tt.Formula || Controller.Instance.Z3.CheckEqual(ct.Formula, tt.Formula))) // needs to be prove
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
                //if (t.Formula == type.Formula || Controller.Instance.Z3.ProveEqual(t.Formula, type.Formula))
                if (t.Formula == type.Formula || Controller.Instance.Z3.ProveContains(t.Formula, type.Formula))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="formula"></param>
        /// <returns></returns>
        public Boolean ContainsTypeFormula(Expr formula)
        {
            foreach (var t in this.Types)
            {
                //if (t.Formula == formula || Controller.Instance.Z3.ProveEqual(t.Formula, formula))
                if (t.Formula == formula || Controller.Instance.Z3.ProveContains(t.Formula, formula))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="N"></param>
        public void MergeSameTypes(uint N)
        {
            foreach (var t in this.Types)
            {
                foreach (var s in this.Types.Except(new SymmetricType[] { t }))
                {
                    // better to remove t rather than find it (faster lookup)
                    //if (s == t)
                    //{
                    //    continue;
                    //}

                    if (t.Formula == s.Formula || Controller.Instance.Z3.ProveContains(t.Formula, s.Formula))
                    //if (t.Formula == s.Formula || Controller.Instance.Z3.ProveEqual(t.Formula, s.Formula))
                    //if (t.Formula == s.Formula || Controller.Instance.Z3.CheckEqual(t.Formula, s.Formula))
                    {
                        t.TN += s.TN;
                        s.TN = 0;
                    }
                }
            }
            this.Types.RemoveWhere(v => v.TN == 0);
            this.CheckTypeSum(N);
        }

        public SymmetricState(uint N, params SymmetricType[] types)
            : this(N, null, null, false, types)
        {
        }

        public SymmetricState(uint N, SymmetricState pre, params SymmetricType[] types)
            : this(N, pre, null, false, types)
        {
        }

        public SymmetricState(uint N, Boolean init, params SymmetricType[] types)
            : this(N, null, null, init, types)
        {
        }

        public SymmetricState(uint N, SymmetricState pre, Transition tau, params SymmetricType[] types)
            : this(N, pre, tau, false, types)
        {
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="N"></param>
        /// <param name="types"></param>
        public SymmetricState(uint N, SymmetricState pre, Transition tau, Boolean init = false, params SymmetricType[] types)
        {
            this.PreState = pre;

            // copy input types
            this.Types = new HashSet<SymmetricType>();
            foreach (var t in types)
            {
                t.Formula = t.Formula.Simplify();
                t.Formula = Controller.Instance.simplifyFormula(t.Formula);
                this.Types.Add(new SymmetricType(t.TN, t.Formula));
            }

            if (this.Types.Any(t => t.Formula.ToString().Contains(Controller.PRIME_SUFFIX)))
            {
                throw new Exception("ERROR: Variable renaming failure.");
            }

            if (this.Types.Any(t => t.Formula.ToString().Contains("#x")))
            {
                throw new Exception("ERROR: discrete location constraint failure (contains #x)." + Environment.NewLine + this);
            }

            this.MergeSameTypes(N);
            if (!this.CheckTypeSum(N))
            {
                throw new Exception("ERROR: sum of type counts not equal to N.");
            }

            this._new = true;
            SymmetricState equal = null;
            foreach (var checkrs in SymmetricState.AllStateTypes)
            {
                if (checkrs.Equals(this))
                {
                    equal = checkrs;
                    this._new = false;
                    break;
                }
            }

            if (this._new)
            {
                SymmetricState.AllStateTypes.Add(this);
            }

            this.CreatedBy = tau;
            this.Initial = init;

            if (pre != null)
            {
                if (this._new)
                {
                    ReachSymmetric.AddEdgeWithTransition(pre, this, tau);
                }
                else // if not new, just add an edge, not another vertex
                {
                    if (equal != null)
                    {
                        ReachSymmetric.AddEdgeWithTransition(pre, equal, tau);
                    }
                }
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

        public enum CreationType { Unknown, Initial, Discrete, Continuous };

        public CreationType CreatedHow = CreationType.Unknown;

        /// <summary>
        /// Returns true if type has been created
        /// </summary>
        /// <param name="f"></param>
        /// <returns></returns>
        public static Boolean ExistingType(Expr f)
        {
            Boolean result = false;
            if (SymmetricType.AllTypes.Contains(f))
            {
                return true;
            }

            foreach (var atype in SymmetricType.AllTypes)
            {
                if (Controller.Instance.Z3.ProveContains(atype, f))
                {
                    return true;
                }
            }
            return false;
        }


        //public static EqualityComparer<SymmetricType> TypeFormulaComparer = new EqualityComparer<SymmetricType>();

        /// <summary>
        /// 
        /// </summary>
        /// <param name="TN"></param>
        /// <param name="Formula"></param>
        public SymmetricType(uint TN, Expr Formula)
        {
            //, StringComparison.CurrentCultureIgnoreCase
            if (Formula.ToString().Contains("exists"))
            {
                throw new Exception("ERROR: quantifier elimination failure (should not contain quantifiers at this step).");
            }

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
        /// Quantify the formula for this type
        /// </summary>
        /// <returns></returns>
        public Expr QuantifyFormula()
        {
            Expr i = Controller.Instance.Indices["i"];
            Expr range = Controller.Instance.Z3.MkAnd(Controller.Instance.Z3.MkGe((ArithExpr)i, (ArithExpr)Controller.Instance.IndexOne), Controller.Instance.Z3.MkLe((ArithExpr)i, (ArithExpr)Controller.Instance.IndexN));
            return Controller.Instance.Z3.MkForall(new Expr[] { i } , Controller.Instance.Z3.MkImplies((BoolExpr)range , (BoolExpr)this.Formula));
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
