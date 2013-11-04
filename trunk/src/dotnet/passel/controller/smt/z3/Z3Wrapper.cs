using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics.Contracts;

using Microsoft.Z3;

using passel.model;

using passel.controller;
using passel.controller.output;
using System.Text.RegularExpressions;

namespace passel.controller.smt.z3
{
    [ContractVerification(true)]
    public class Z3Wrapper : Microsoft.Z3.Context
    {
        public Z3Wrapper(Dictionary<string,string> c)
            : base(c)
        {
            this.Assumptions = new List<BoolExpr>();
            this.AssumptionsUniversal = new List<BoolExpr>();
            //this.slvr = this.MkSolver();
            //this.slvr = this.MkSimpleSolver();
            // doesn't seem to allow nested tactics.... (apply (then simplify propagate-values split-clause propagate-ineqs))

            Tactic t;
            Params p;

            p = this.MkParams();
            p.Add("qe-nonlinear", true);
            p.Add("produce-models", true);
            p.Add("candidate-models", true);
            p.Add("mbqi", true);
            p.Add("auto-config", false);
            p.Add("ematching", true);
            p.Add("pull-nested-quantifiers", true);
            p.Add("distribute-forall", true);
            p.Add("pi-pull-quantifiers", true);

            p.Add("hi-div0", true);
            p.Add("relevancy", true);
            p.Add("qi-eager-threshold", 1000);
            p.Add("qi-lazy-threshold", 1000);
            Tactic tsimplify = this.With(this.MkTactic("simplify"), p);
            tsimplify = this.OrElse(tsimplify, this.MkTactic("skip"));

            //p = this.MkParams();



            Tactic tqe = this.With(this.MkTactic("qe"), p);
            tqe = this.OrElse(tqe, this.MkTactic("skip"));

            //p = this.MkParams();
            //Tactic tfm = this.With(this.MkTactic("fm"), p);
            //tfm = this.OrElse(tfm, this.MkTactic("skip"));

            //p = this.MkParams();
            //p.Add("pull-cheap-ite", true);
            Tactic tctxsimplify = this.With(this.MkTactic("ctx-simplify"), p);
            tctxsimplify = this.OrElse(tctxsimplify, this.MkTactic("skip"));

            //p = this.MkParams();
            Tactic tpreprocess = this.With(this.MkTactic("sat-preprocess"), p);
            tpreprocess = this.OrElse(tpreprocess, this.MkTactic("skip"));

            // some bug with distribute-forall, all become false
            //p = this.MkParams();
            Tactic tdistributeForall = this.With(this.MkTactic("distribute-forall"), p); // all false
            string[] alltactics = TacticNames;
            //Tactic tdistributeForall = this.MkTactic("add-bounds"); // all false
            //Tactic tdistributeForall = this.MkTactic("qfnra");
            //Tactic tdistributeForall = this.MkTactic("qflra"); 

            //string[] ts = { "nlsat", "split-clause", "der", "normalize-bounds", "qfnra", "qflra", "symmetry-reduce", "qfnia", "qflia", "diff-neq", "purify-arith", "max-bv-sharing", "elim-term-ite", "propagate-values", "elim-and", "elim-uncnstr" };
            //string[] ts = { "nlsat", "qe-sat", "split-clause", "der", "normalize-bounds", "qfnra", "qflra", "symmetry-reduce", "qfnia", "qflia", "diff-neq", "purify-arith", "max-bv-sharing", "elim-term-ite", "propagate-values", "elim-and", "elim-uncnstr" };

            //string[] ts = { "nlsat", "qe-sat", "diff-neq", "purify-arith" };
            //string[] ts = { "nlsat", "qe-sat" };
            //string[] ts = {  "qe-sat" };

            //List<Tactic> lts = new List<Tactic>();
            //foreach (var a in ts)
            //{
            //    lts.Add(this.OrElse(this.MkTactic(a), this.MkTactic("skip")));
            //}

            //tdistributeForall = this.OrElse(tdistributeForall, this.MkTactic("skip"));

            //p = this.MkParams();
            Tactic tvsubst = this.With(this.MkTactic("vsubst"), p);
            tvsubst = this.OrElse(tvsubst, this.MkTactic("skip"));

            

            //pull-nested-quantifiers
            Tactic tsmt = this.With(this.MkTactic("smt"), p);
            //tsmt = this.OrElse(tsmt, this.MkTactic("skip"));

            //t = this.Repeat(this.ParOr(tqe, tsmt));
            //t = this.With(this.Repeat(this.Then(tqe, tsmt)), p);


            //p = this.MkParams();

            t = this.With(this.Repeat(this.Then(tsimplify, tctxsimplify, tdistributeForall, tpreprocess, tqe, tvsubst, tsmt)), p);
            //lts.AddRange(new Tactic[] {tsimplify, tctxsimplify, tpreprocess, tqe, tvsubst, tsmt});
            //Tactic[] tsmore = lts.GetRange(2, lts.Count - 2).ToArray();
            //t = this.With(this.Repeat(this.Then(lts[0], lts[1], tsmore)), p);
            

            //this.slvr = t.Solver;


            /*
             * NOTES: 2012/11/27
             * 
             * Previously, we had been using this.MkSolver(), which would return a default solver with the appropriate tactics as specified by global configuration parameters.
             * However, more recent versions of Z3 have disabled some of these (particularly the ELIM_QUANT option), which caused problems for some transitions.
             * 
             * The key solvers appear to be: smt, qe, and qe-sat
             */

            //this.slvr = this.MkSolver(t);

            //System.Console.WriteLine("Custom tactic options:");
            //System.Console.WriteLine(this.slvr.Help);
            //System.Console.WriteLine(this.slvr.ParameterDescriptions);

            if (Controller.OldApiParameters())
            {
                this.slvr = this.MkSolver(); // (par-or smt qe)
            }
            else
            {
                this.slvr = this.MkSolver();
                //this.slvr = t.Solver;
            }

            //System.Console.WriteLine("Default tactic options:");
            //System.Console.WriteLine(this.slvr.Help);
            //ParamDescrs pd = this.slvr.ParameterDescriptions;
            //System.Console.WriteLine(this.slvr.ParameterDescriptions);
            
            

            //Params origParams = this.slvr.Parameters;



            //this.slvr.Parameters.Add("mbqi", true);
        }

        /**
         * Asserted assumptions
         */
        public List<BoolExpr> Assumptions;

        /**
         * Basic data type assumptions needed even for unquantified tasks (e.g., reach set projection)
         */
        public List<BoolExpr> AssumptionsUniversal;

        public Solver slvr;

        /**
        * Replace all references to a function declaration in a tree of terms
        */
        public void replaceFuncDecl(ref Expr origReplaced, Expr orig, FuncDecl find, FuncDecl replace, Boolean byString)
        {
            Contract.Requires(origReplaced != null);
            Contract.Requires(orig != null);
            Contract.Requires(find != null);
            Contract.Requires(replace != null);

            if (orig.ASTKind == Z3_ast_kind.Z3_APP_AST && orig.FuncDecl.Equals(find) || (byString && orig.ToString().Equals(find.ToString())))
            {
                origReplaced = Controller.Instance.Z3.MkApp(replace, orig.Args);
            }
            try
            {
                Expr[] ts = null;

                switch (orig.ASTKind)
                {
                    case Z3_ast_kind.Z3_QUANTIFIER_AST:
                        Quantifier q = (Quantifier)orig;
                        //ts = new Term[] { orig.GetQuantifier().Body }; // can't do it this way: we need a pointer to the original memory!
                        ts = new Expr[] { q.Body };
                            
                        break;
                    case Z3_ast_kind.Z3_APP_AST:
                        //FuncDecl fd = orig.GetAppDecl(); // todo: do the replacement on this---make another function do this replacement only for priming and unpriming (will be much faster)
                        ts = orig.Args;
                        break;
                    case Z3_ast_kind.Z3_NUMERAL_AST: // bottom of tree
                        return;
                    case Z3_ast_kind.Z3_VAR_AST:
                        return;
                    default:
                        return;
                }

                if (ts != null)
                {
                    for (int i = 0; i < ts.Length; i++)
                    {
                        replaceFuncDecl(ref ts[i], ts[i], find, replace, byString);
                    }
                }

                // call term modifier from api

                // quantifiers are very nasty to deal with (due to renaming bound variables in scope, etc.)
                if (origReplaced.ASTKind == Z3_ast_kind.Z3_QUANTIFIER_AST)
                {
                    Quantifier q = (Quantifier)origReplaced; // todo: check
                    origReplaced = Controller.Instance.Z3.MkQuantifier(q.IsUniversal, q.BoundVariableSorts, q.BoundVariableNames, ts[0]);
                }
                else
                {
                    origReplaced.Update(ts);
                    //origReplaced = origReplaced.Substitute(new Expr[] {origReplaced}, ts); // todo: check if correct
                }
            }
            catch (Microsoft.Z3.Z3Exception e)
            {
            }
        }

        /**
         * Replace a term in a tree of terms
         * DEPRECATED BY Z3 4.0 Expr.Substitute(from,to)
         *
        public void replaceTerm(ref Expr origReplaced, Expr orig, Expr find, Expr replace, Boolean byString)
        {
            if (orig != null)
            {
                if (orig.Equals(find) || orig == find || (byString && orig.ToString().Equals(find.ToString())))
                {
                    origReplaced = replace;
                    return;
                }
                try
                {
                    Expr[] ts;

                    switch (orig.ASTKind)
                    {
                        case Z3_ast_kind.Z3_QUANTIFIER_AST:
                            ts = new Expr[] { ((Quantifier)orig).Body };
                            break;
                        case Z3_ast_kind.Z3_APP_AST:
                            FuncDecl fd = orig.FuncDecl; // TODO: do the replacement on this---make another function do this replacement only for priming and unpriming (will be much faster)
                            ts = orig.Args;
                            break;
                        case Z3_ast_kind.Z3_NUMERAL_AST: // bottom of tree
                            return;
                        case Z3_ast_kind.Z3_VAR_AST:
                            return;
                        default:
                            return;
                    }

                    for (int i = 0; i < ts.Length; i++)
                    {
                        replaceTerm(ref ts[i], ts[i], find, replace, byString);
                    }

                    // call term modifier from api
                    //if (origReplaced != orig)
                    //{

                    // quantifiers are very nasty to deal with (due to renaming bound variables in scope, etc.)
                    if (origReplaced.ASTKind == Z3_ast_kind.Z3_QUANTIFIER_AST)
                    {
                        Quantifier q = (Quantifier)origReplaced; // TODO: check
                        origReplaced = Controller.Instance.Z3.MkQuantifier(q.IsUniversal, q.BoundVariableSorts, q.BoundVariableNames, ts[0]);
                    }
                    else
                    {
                        origReplaced.Update(ts);
                        //origReplaced = this.UpdateTerm(origReplaced, ts); // TODO: fix
                        //origReplaced = origReplaced.Substitute(new Expr[] { origReplaced }, ts); // todo: check if correct
                    }
                    //}
                }
                catch (Microsoft.Z3.Z3Exception e)
                {
                }
            }
        }

         * */

        /**
         * Find all global variables that are primed in the reset and exclude them from the identity for transitions
         */
        public List<String> findGlobalVariableResets(Expr reset)
        {
            List<String> vars = new List<String>();

            foreach (var v in Controller.Instance.GlobalVariablesPrimed)
            {
                if (!this.findTerm(reset, v.Value, false))
                {
                    vars.Add(v.Key);
                }
            }
            return vars;
        }

        /**
         * Find all indexed variables that are primed in the reset and exclude them from the identity for transitions of the process making the move
         * Example: a process h may move from state a to b, but the clock x[h] may not be reset on this state, thus we must enforce x'[h] = x[h] (counterexamples otherwise)
         */
        public List<String> findIndexedVariableResets(Expr reset)
        {
            List<String> vars = new List<String>();

            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDeclPrimed)
                        {
                            if (!v.Key.Contains("q") && !this.findFunc(reset, v.Key, false))
                            {
                                vars.Add(v.Key);
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDeclPrimed)
                        {
                            if (!v.Key.Contains("q") && !this.findFunc(reset, v.Key, false))
                            {
                                vars.Add(v.Key);
                            }
                        }
                        break;
                    }
            }
            return vars;
        }


        public List<String> findIndexedVariableResetsNeg(Expr reset)
        {
            List<String> vars = new List<String>();

            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDeclPrimed)
                        {
                            if (this.findFunc(reset, v.Key, true))
                            {
                                vars.Add(v.Key);
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDeclPrimed)
                        {
                            if (this.findFunc(reset, v.Key, true))
                            {
                                vars.Add(v.Key);
                            }
                        }
                        break;
                    }
            }
            return vars;
        }


        /**
         * Determine whether a particular function declaration appears in a tree of terms
         */
        public Boolean findFunc(Expr haystack, String needle, Boolean byString)
        {
            // todo: horrible hack: just search by string
            if (haystack == null)
            {
                return false;
            }
            else
            {
                String t1 = haystack.ToString();
                return (haystack.ToString().Contains(needle + Controller.PRIME_SUFFIX));
            }

            /*
            if (haystack != null)
            {
                if (haystack.Equals(needle) || haystack == needle || (byString && haystack.ToString().Equals(needle.ToString())))
                {
                    return true;
                }
                try
                {
                    Term[] ts;

                    switch (haystack.GetKind())
                    {
                        case TermKind.Quantifier:
                            ts = new Term[] { haystack.GetQuantifier().Body };
                            break;
                        case TermKind.App:
                            FuncDecl fd = haystack.GetAppDecl(); // todo: do the replacement on this---make another function do this replacement only for priming and unpriming (will be much faster)
                            ts = haystack.GetAppArgs();
                            break;
                        case TermKind.Numeral: // bottom of tree
                            return false;
                        case TermKind.Var:
                            return false;
                        default:
                            return false;
                    }

                    for (int i = 0; i < ts.Length; i++)
                    {
                        return findTerm(ts[i], needle, byString);
                    }
                }
                catch (Microsoft.Z3.Z3Error e)
                {
                }
            }
            return false;*/
        }

        /**
        * Determine if a term exists in a tree off terms
        */
        public Boolean findTerm(Expr haystack, Expr needle, Boolean byString)
        {
            // todo: horrible hack: just search by string
            if (haystack == null)
            {
                return false;
            }
            else
            {
                return (haystack.ToString().Contains(needle.ToString()));
            }

            /*
            if (haystack != null)
            {
                if (haystack.Equals(needle) || haystack == needle || (byString && haystack.ToString().Equals(needle.ToString())))
                {
                    return true;
                }
                try
                {
                    Term[] ts;

                    switch (haystack.GetKind())
                    {
                        case TermKind.Quantifier:
                            ts = new Term[] { haystack.GetQuantifier().Body };
                            break;
                        case TermKind.App:
                            FuncDecl fd = haystack.GetAppDecl(); // todo: do the replacement on this---make another function do this replacement only for priming and unpriming (will be much faster)
                            ts = haystack.GetAppArgs();
                            break;
                        case TermKind.Numeral: // bottom of tree
                            return false;
                        case TermKind.Var:
                            return false;
                        default:
                            return false;
                    }

                    for (int i = 0; i < ts.Length; i++)
                    {
                        return findTerm(ts[i], needle, byString);
                    }
                }
                catch (Microsoft.Z3.Z3Error e)
                {
                }
            }
            return false;*/
        }

        /**
         * Hack to deep copy a formula
         */
        public Expr copyExpr(Expr orig)
        {
            Contract.Requires(orig != null);
            // huge hack to avoid clobbering original formula with pass-by-reference
            // we create a new z3 context and "translate" (copy) the term to that context, then copy it back
            // we cannot just "translate" to the same context, because it checks if the context is the same and returns the original reference if so
            Context tmpcontext = new Context(Controller.Instance.Config);
            Expr fcopy = orig.Translate(tmpcontext);
            Expr fcopyback = fcopy.Translate(this);
            return fcopyback;
        }

        

        /**
         * Prime all variables
         */
        public void primeAllVariables(ref Expr origReplaced)
        {
            Contract.Requires(origReplaced != null);

            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key]);
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            //origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key]);
                            replaceFuncDecl(ref origReplaced, origReplaced, v.Value, Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], false); // TODO: also buggy, doesn't replace properly
                        }
                         
                        /*
                        foreach (var v in Controller.Instance.IndexedVariables)
                        {
                            KeyValuePair<string,string> k = new KeyValuePair<string,string>(v.Key.Key + Controller.PRIME_SUFFIX, v.Key.Value);
                            /*if (origReplaced.IsQuantifier)
                            {
                                foreach (Symbol idx in ((Quantifier)origReplaced).BoundVariableNames)
                                {
                                    Expr vconst = Controller.Instance.Z3.MkConst(":var 0", ((Quantifier)origReplaced).BoundVariableSorts[0]);
                                    Expr app = Controller.Instance.Z3.MkApp(v.Value.FuncDecl, new Expr[] {  vconst});
                                    origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.IndexedVariablesPrimed[k]);
                                }
                            }
                            else
                            {***** /
                            origReplaced = origReplaced.SubstituteVars(new Expr[] { Controller.Instance.IndexedVariablesPrimed[k]});
                                origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.IndexedVariablesPrimed[k]);
                            //}
                        }*/
                        break;
                    }
            }

            foreach (var v in Controller.Instance.GlobalVariablesPrimed) // uses primed from earlier revision before global variables added in more coherent manner (were parameters with update_type)
            {
                origReplaced = origReplaced.Substitute(Controller.Instance.GlobalVariables[v.Key], v.Value);
            }
        }

        private static Dictionary<Expr, Expr> CacheProjectGlobals = new Dictionary<Expr, Expr>();

        public Expr projectAwayGlobals(Expr f)
        {
            if (CacheProjectGlobals.ContainsKey(f))
            {
                return CacheProjectGlobals[f];
            }
            Tactic tqe = this.MkTactic("qe");
            Goal g = this.MkGoal();
            List<Expr> bound = Controller.Instance.GlobalVariables.Values.ToList();
            BoolExpr qe = this.MkExists(bound.ToArray(), f);


            List<BoolExpr> remAss = this.Assumptions.FindAll(a => a.IsQuantifier); // todo: add type constraints to constant (q_i) instead of functions (q i)
            this.Assumptions.RemoveAll(a => a.IsQuantifier); // otherwise q.e. will fail
            g.Assert(this.Assumptions.ToArray());
            this.Assumptions.AddRange(remAss); // add back
            g.Assert(this.AssumptionsUniversal.ToArray());
            g = g.Simplify();


            g.Assert(qe);
            ApplyResult ar = tqe.Apply(g);
            List<BoolExpr> res = new List<BoolExpr>();
            foreach (var v in ar.Subgoals)
            {
                res.AddRange(v.Formulas);
            }

            res.RemoveAll(fa => this.Assumptions.Contains(fa));
            res.RemoveAll(fa => this.AssumptionsUniversal.Contains(fa));

            Expr nr = this.MkAnd(res.ToArray());

            // assumptions may have added primed variables
            this.unprimeAllVariables(ref nr);
            nr = nr.Simplify();

            Z3Wrapper.CacheProjectGlobals.Add(f, nr); 
            return nr;
        }

        private static Dictionary<Tuple<Expr, List<Expr>>, Expr> CacheProject = new Dictionary<Tuple<Expr, List<Expr>>, Expr>();

        // project away given variables
        public Expr projectAway(Expr f, List<Expr> vars)
        {
            // no change
            if (vars.Count == 0)
            {
                return f;
            }

            Tuple<Expr, List<Expr>> key = new Tuple<Expr, List<Expr>>(f, vars);
            if (CacheProject.ContainsKey(key))
            {
                return CacheProject[key];
            }

            Expr newF = this.copyExpr(f);

            // HACK: replace all location names with their values...
            foreach (var loc in Controller.Instance.Sys.HybridAutomata[0].Locations)
            {
                newF = newF.Substitute(loc.LabelExpr, loc.BitVectorExpr);
            }
            newF = newF.Substitute(Controller.Instance.IndexN, Controller.Instance.Z3.MkInt(Controller.Instance.IndexNValue));

            Params p = this.MkParams();
            p.Add("qe-nonlinear", true);
            p.Add("eliminate-variables-as-block", false);
            //Tactic tqe = Controller.Instance.Z3.Repeat(Controller.Instance.Z3.MkTactic("qe"));
            Tactic tqe = Controller.Instance.Z3.With(this.MkTactic("qe"), p);
            tqe = Controller.Instance.Z3.Repeat(this.Then(this.MkTactic("ctx-simplify"), tqe));
            
            Goal g = this.MkGoal();

            List<BoolExpr> remAss = this.Assumptions.FindAll(a => a.IsQuantifier); // todo: add type constraints to constant (q_i) instead of functions (q i)
            this.Assumptions.RemoveAll(a => a.IsQuantifier); // otherwise q.e. will fail
            g.Assert(this.Assumptions.ToArray());


            //TODO: add the discrete locations constraints to the constants now, has to be done


            this.Assumptions.AddRange(remAss); // add back
            g.Assert(this.AssumptionsUniversal.ToArray());
            g = g.Simplify();

            Expr qe = Controller.Instance.Z3.MkExists(vars.ToArray(), (BoolExpr)newF);
            System.Console.WriteLine(qe);

            g.Assert((BoolExpr)qe);
            ApplyResult ar = tqe.Apply(g);

            List<BoolExpr> projected = new List<BoolExpr>();
            foreach (var sg in ar.Subgoals)
            {
                projected.AddRange(sg.Formulas);
            }

            projected.RemoveAll(fa => this.Assumptions.Contains(fa));
            projected.RemoveAll(fa => this.AssumptionsUniversal.Contains(fa));

            newF = Controller.Instance.Z3.MkAnd(projected.ToArray());

            // HACK: replace all location values with their names...
            // todo: this could be bad
            foreach (var loc in Controller.Instance.Sys.HybridAutomata[0].Locations)
            {
                newF = newF.Substitute(loc.BitVectorExpr, loc.LabelExpr);
            }
            //newF = newF.Substitute(Controller.Instance.Z3.MkInt(Controller.Instance.IndexNValue), Controller.Instance.IndexN); // todo: this could be bad to do...            

            if (newF.ToString().Contains("#x"))
            {
                throw new Exception("Discrete location problem");
            }

            // assumptions may have added primed variables
            this.unprimeAllVariables(ref newF);

            newF = newF.Simplify();



            CacheProject.Add(key, newF);

            return newF;
        }

        private static Dictionary<Expr, Expr> CacheProjectIndex = new Dictionary<Expr, Expr>();

        // project away all index variables
        public Expr projectAwayIndexVariables(Expr f)
        {
            if (CacheProjectIndex.ContainsKey(f))
            {
                return CacheProjectIndex[f];
            }

            List<Expr> bound = new List<Expr>();
            Expr idx = Controller.Instance.Indices["i"];
            Expr newF = this.copyExpr(f);

            foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
            {
                Expr varConst = Controller.Instance.Z3.MkConst(v.Name + "_" + "i", v.TypeSort);
                newF = newF.Substitute(Controller.Instance.Z3.MkApp(v.Value, idx), varConst);
                bound.Add(varConst);
            }

            foreach (var v in Controller.Instance.Params)
            {
                if (v.Key != "N")
                {
                    bound.Add(v.Value);
                }
            }

            Tactic tqe = Controller.Instance.Z3.Repeat(Controller.Instance.Z3.MkTactic("qe"));
            Goal g = Controller.Instance.Z3.MkGoal();


            List<BoolExpr> remAss = this.Assumptions.FindAll(a => a.IsQuantifier); // todo: add type constraints to constant (q_i) instead of functions (q i)
            this.Assumptions.RemoveAll(a => a.IsQuantifier); // otherwise q.e. will fail
            g.Assert(this.Assumptions.ToArray());
            this.Assumptions.AddRange(remAss); // add back
            g.Assert(this.AssumptionsUniversal.ToArray());
            g = g.Simplify();


            Expr qe = Controller.Instance.Z3.MkExists(bound.ToArray(), (BoolExpr)newF);

            g.Assert((BoolExpr)qe);
            ApplyResult ar = tqe.Apply(g);

            List<BoolExpr> projected = new List<BoolExpr>();
            foreach (var sg in ar.Subgoals)
            {
                projected.AddRange(sg.Formulas);
            }

            projected.RemoveAll(fa => this.Assumptions.Contains(fa));
            projected.RemoveAll(fa => this.AssumptionsUniversal.Contains(fa));

            newF = Controller.Instance.Z3.MkAnd(projected.ToArray());

            // convert constants back to functions
            foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
            {
                Expr varConst = Controller.Instance.Z3.MkConst(v.Name + "_" + "i", v.TypeSort);
                newF = newF.Substitute(varConst, Controller.Instance.Z3.MkApp(v.Value, idx));
            }

            // assumptions may have added primed variables
            this.unprimeAllVariables(ref newF);
            newF = newF.Simplify();

            CacheProjectIndex.Add(f, newF);

            return newF;
        }

        /**
         * abstract global indexed variables
         */
        public Expr abstractGlobals(Expr f, uint N, uint projectN, uint i, uint j)
        {
            Contract.Requires(f != null);

            // TODO: SPECIAL CARE MUST BE TAKEN DEFINITELY FOR INDEX-VALUED GLOBAL VARIABLES, AND POSSIBLY ALSO FOR INDEXED CONTROL LOCATION VARIABLES....

            Debug.Write("Property before abstracting index variables: ");
            Debug.Write(f.ToString() + "\n\r\n\r");

            Expr iidx = this.MkIntConst("i");
            Expr jidx = this.MkIntConst("j");

            // TODO: GENERALIZE
            foreach (var v in Controller.Instance.Sys.Variables)
            {
                if (v.Type == Variable.VarType.index)
                {
                    Expr gv = Controller.Instance.GlobalVariables[v.Name];

                    //RAND BUG: COMMENT NEXT
                    //f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkTrue()); // weakeast abstraction
                    //f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkFalse()); // weakeast abstraction




                    //f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkNot(this.MkEq(gv, iidx)));
                    //f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexOne), this.MkEq(gv, iidx));

                    if (projectN == 1)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx)); // 1 -> i
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkNot(this.MkEq(gv, iidx))); // 2 -> not i
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkNot(this.MkEq(gv, iidx))); // 3 -> not i
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, iidx)); // 2 -> i
                        
                        
                        
                        //RAND BUG: COMMENT NEXT
                        f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkTrue()); // 2 -> null



                        f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkNot(this.MkEq(gv, iidx)));
                    }

                    if (projectN == 2)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx)); // 1 -> i
                        f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx)); // 2 -> j


                        f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkTrue()); // 3 -> null

                        f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx)))); // 0 -> not i and not j

                        // RAND BUG: COMMENT NEXT
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx)))); // 3 -> not i
                    }



                    if (i == 1)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx));
                    }
                    if (projectN > 1 && j == 0 && i == 2)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx));
                    }

                    if (j > 0 && j == 1)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx));
                    }
                    if (projectN > 1 && j > 0 && j == 2)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx));
                    }

                    // replace all other indices with true
                    for (int x = 1; x <= N; x++)
                    {
                        if (x == i || x == j)
                        {
                            //continue;
                        }
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkTrue()); // weakest

                        if (projectN == 1)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkNot(this.MkEq(gv, iidx)));
                        }
                        else if (projectN == 2)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx)))); // 0 -> not i and not j
                        }


                        // this is what arons2001cav does
                        /*if (projectN > 1)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx))));
                        }
                        else
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkNot(this.MkEq(gv, iidx)));
                        }*/
                    }

                    /*

                    if (projectN == 1)
                    {
                        f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkTrue()); // weakeast abstraction
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkNot(this.MkEq(gv, iidx)));
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkGt((ArithExpr)gv, (ArithExpr)iidx));
                    }
                    else
                    {
                        //f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx));
                        f = f.Substitute(this.MkEq(gv, this.MkInt(j)), this.MkEq(gv, jidx));
                    }
                    //f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkTrue()); // weakeast abstraction
                    //f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx))));
                    //f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkAnd(this.MkGt((ArithExpr)gv, (ArithExpr)iidx), this.MkGt((ArithExpr)gv, (ArithExpr)jidx)));

                    //f = f.Substitute(this.MkEq(gv, this.MkInt(4)), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx))));
                    // TODO: > 4 cases, inequality cases, non-equality cases
                     */
                }
            }


            // replace local index-value variables
            foreach (var v in Controller.Instance.Sys.HybridAutomata[0].Variables)
            {
                if (v.Type == Variable.VarType.index)
                {
                    foreach (var iv in Controller.Instance.IndexedVariables)
                    {
                        if (v.Name != iv.Key.Key)
                        {
                            continue;
                        }
                        Expr gv = iv.Value;

                        if (projectN == 1)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx)); // 1 -> i

                            f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkTrue()); // 2 -> null

                            f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkNot(this.MkEq(gv, iidx)));
                        }

                        if (projectN == 2)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx)); // 1 -> i
                            f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx)); // 2 -> j


                            f = f.Substitute(this.MkEq(gv, this.MkInt(3)), this.MkTrue()); // 3 -> null

                            f = f.Substitute(this.MkEq(gv, Controller.Instance.IndexNone), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx)))); // 0 -> not i and not j
                        }

                        if (i == 1)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx));
                        }
                        if (projectN > 1 && j == 0 && i == 2)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx));
                        }

                        if (j > 0 && j == 1)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(1)), this.MkEq(gv, iidx));
                        }
                        if (projectN > 1 && j > 0 && j == 2)
                        {
                            f = f.Substitute(this.MkEq(gv, this.MkInt(2)), this.MkEq(gv, jidx));
                        }

                        // replace all other indices with true
                        for (int x = 1; x <= N; x++)
                        {
                            if (x == i || x == j)
                            {
                                //continue;
                            }
                            //f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkTrue()); // weakest

                            if (projectN == 1)
                            {
                                f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkNot(this.MkEq(gv, iidx)));
                            }
                            else if (projectN == 2)
                            {
                                f = f.Substitute(this.MkEq(gv, this.MkInt(x)), this.MkAnd(this.MkNot(this.MkEq(gv, iidx)), this.MkNot(this.MkEq(gv, jidx)))); // 0 -> not i and not j
                            }
                        }
                    }
                    
                }
            }

            Debug.Write("Property after abstracting index variables: ", Debug.VERBOSE_STEPS);
            Debug.Write(f.ToString() + "\n\r\n\r", Debug.VERBOSE_STEPS);

            return f;
        }

        /**
         * Generalization step from a finite instantiation reach set to a quantified predicate
         * 
         * N is the number of processes in the finite instantiation
         * 
         * Assumes original term has already been projected onto a small instance
         */
        public void generalizeAllVariables(ref Expr origReplaced, uint N)
        {/*
            if (origReplaced.IsOr)
            {
                //origReplaced = origReplaced.Args[0]; // TODO: CHECK GENERALITY
                for (int i = 0; i < origReplaced.NumArgs; i++)
                {
                    if (origReplaced.Args[i].IsTrue)
                    {
                        Expr[] copy = origReplaced.Args;
                        copy[i] = MkFalse();
                        origReplaced.Update(copy);
                    }
                }
            }*/

            for (int i = 1; i <= N; i++)
            {
                switch (Controller.Instance.DataOption)
                {
                    case Controller.DataOptionType.array:
                        {
                            // TODO
                            break;
                        }
                    case Controller.DataOptionType.uninterpreted_function:
                    default:
                        {
                            foreach (var v in Controller.Instance.UndefinedVariables)
                            {
                                if (v.Key.Contains(i.ToString()))
                                {
                                    int idx = 'i' + i - 1;
                                    string sidx = ((char)idx).ToString();
                                    string varname = Regex.Replace(v.Key, "[\\d+]", ""); // strip all numbers TODO: generalize to allow numbers in variable names
                                    KeyValuePair<string,string> kv = new KeyValuePair<string, string>(varname, sidx);
                                    origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.IndexedVariables[kv]);
                                }
                            }
                            break;
                        }
                }
            }

            /*
            foreach (var v in Controller.Instance.GlobalVariablesPrimed) // uses primed from earlier revision before global variables added in more coherent manner (were parameters with update_type)
            {
                origReplaced = origReplaced.Substitute(Controller.Instance.GlobalVariables[v.Key], v.Value);
            }
             */
        }




        /**
         * Unprime all variables
         */
        public void unprimeAllVariables(ref Expr origReplaced)
        {
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDeclPrimed)
                        {
                            origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.DataA.IndexedVariableDecl[v.Key]);
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDeclPrimed)
                        {
                            replaceFuncDecl(ref origReplaced, origReplaced, v.Value, Controller.Instance.DataU.IndexedVariableDecl[v.Key], false);
                        }
/*                        foreach (var v in Controller.Instance.IndexedVariables)
                        {
                            origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.IndexedVariablesPrimed[v.Key]); // buggy, substitute doesn't work properly on bound variables of quantifiers
                        }
 */
                        break;
                    }
            }

            foreach (var v in Controller.Instance.GlobalVariables) // uses primed from earlier revision before global variables added in more coherent manner (were parameters with update_type)
            {
                origReplaced = origReplaced.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Key], v.Value);
            }
        }

        /**
         * Unprime all variables, replace with state at round k, and others with state at round k-1
         * 
         * TODO: refactor and merge with other unprime
         */
        public void unprimeAllVariables(ref Expr origReplaced, uint k)
        {
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDeclPrimed)
                        {
                            // todo: fix for array modeling
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        // replace unprimed by pre-state index
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            FuncDecl preState = Controller.Instance.Z3.MkFuncDecl(v.Key + (k).ToString(), v.Value.Domain, v.Value.Range);
                            replaceFuncDecl(ref origReplaced, origReplaced, v.Value, preState, false);
                        }
                        // replace primed by post-state index (todo: merge with previous loop)
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDeclPrimed)
                        {
                            FuncDecl postState = Controller.Instance.Z3.MkFuncDecl(v.Key + (k+1).ToString(), v.Value.Domain, v.Value.Range);
                            replaceFuncDecl(ref origReplaced, origReplaced, v.Value, postState, false);
                        }
                        break;
                    }
            }

            foreach (var v in Controller.Instance.GlobalVariables) // uses primed from earlier revision before global variables added in more coherent manner (were parameters with update_type)
            {
                Expr preState = Controller.Instance.Z3.MkConst(v.Key + (k).ToString(), v.Value.Sort); // todo: make sure constructed as appropriately typed sorts, not uninterpreted...
                Expr postState = Controller.Instance.Z3.MkConst(v.Key + (k+1).ToString(), v.Value.Sort);
                origReplaced = origReplaced.Substitute(v.Value, preState);
                origReplaced = origReplaced.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Key], postState);
            }
        }


        /**
         * Unprime all variables, replace with state at round k, and others with state at round k-1
         * 
         * TODO: refactor and merge with other unprime
         */
        public void unprimeAllVariablesReachability(ref Expr origReplaced, uint k, uint kFrom)
        {
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDeclPrimed)
                        {
                            // todo: fix for array modeling
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        // replace unprimed by pre-state index
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            FuncDecl preState = Controller.Instance.Z3.MkFuncDecl(v.Key + (k).ToString(), v.Value.Domain, v.Value.Range);
                            FuncDecl preStateFrom = Controller.Instance.Z3.MkFuncDecl(v.Key + (kFrom).ToString(), v.Value.Domain, v.Value.Range);
                            replaceFuncDecl(ref origReplaced, origReplaced, preStateFrom, preState, false);
                        }
                        break;
                    }
            }

            foreach (var v in Controller.Instance.GlobalVariables) // uses primed from earlier revision before global variables added in more coherent manner (were parameters with update_type)
            {
                Expr preState = Controller.Instance.Z3.MkConst(v.Key + (k).ToString(), v.Value.Sort); // todo: make sure constructed as appropriately typed sorts, not uninterpreted...
                Expr preStateFrom = Controller.Instance.Z3.MkConst(v.Key + (kFrom).ToString(), v.Value.Sort); // todo: make sure constructed as appropriately typed sorts, not uninterpreted...
                origReplaced = origReplaced.Substitute(preStateFrom, preState);           
            }
        }

        /**
         * Distinct terms
         */
        public Expr MkDistinct(Expr t1, Expr t2)
        {
            return this.MkDistinct(new Expr[] { t1, t2 });
        }

        public Expr replaceIndices(Expr t, Expr[] oldIndices, Expr[] newIndices)
        {
            uint c = uint.MaxValue;

            if (oldIndices.Length == oldIndices.Length)
            {
                Expr[] placeholder = new Expr[oldIndices.Length];
                for (int i = 0; i < oldIndices.Length; i++)
                {
                    placeholder[i] = this.MkInt(c);
                    t = t.Substitute(oldIndices[i], placeholder[i]); // i -> p
                    c--;
                }

                for (int i = 0; i < oldIndices.Length; i++)
                {
                    t = t.Substitute(placeholder[i], newIndices[i]); // p -> j
                }
            }
            return t;
        }

        /**
         * Macro for a simple max term: if a >= b, then return a, else return b
         */
        public Expr MkMax(Expr a, Expr b)
        {
            return this.MkITE( this.MkGe((ArithExpr)a, (ArithExpr)b), a, b);
        }

        /**
         * Macro for a simple min term: if a <= b, then return a, else return b
         */
        public Expr MkMin(Expr a, Expr b)
        {
            return this.MkITE( this.MkLe((ArithExpr)a, (ArithExpr)b), a, b);
        }

        public Boolean checkTerm(Expr t)
        {
            Model m;
            Expr[] c;
            return checkTerm(t, out m, out c);
        }

        public Boolean checkTerm(Expr t, out Model model)
        {
            Expr[] c;
            return checkTerm(t, out model, out c);
        }

        /**
         * Check a term
         */
        public Boolean checkTerm(Expr t, out Model model, out Expr[] core)
        {
            model = null;
            core = null;
            Boolean ret = false;

            Debug.Write("Term:\n\r" + t.ToString(), Debug.VERBOSE_ALL);

            //this.slvr = this.MkSolver(); // WAY slower
            //this.slvr.Assert(this.Assumptions.ToArray());

            // save the current state of the context
            this.slvr.Push();

            this.slvr.Assert((BoolExpr)t);
            Expr[] assumptions = null;
            //Term[] assumptions = new Term[] { t };

            Expr proof = null;
            //switch (this.CheckAndGetModel(out model))
            //switch (this.CheckAssumptions(out model, new Term[] {this.GetAssignments()}, out proof, out core))
            switch (this.slvr.Check())
            {
                case Status.UNSATISFIABLE:
                    Debug.Write("unsat", Debug.VERBOSE_STEPS);
                    ret = false;
                    core = slvr.UnsatCore;
                    break;
                case Status.UNKNOWN:
                    Debug.Write("WARNING: unknown", Debug.MINIMAL);
                    Debug.Write("Term:\n\r" + t.ToString(), Debug.MINIMAL);
                    ret = true; // may occur semantics
                    break;
                case Status.SATISFIABLE:
                    Debug.Write("sat", Debug.VERBOSE_STEPS);
                    Debug.Write("model: \n\r" + slvr.Model.ToString(), Debug.VERBOSE_ALL);
                    ret = true;
                    model = slvr.Model;
                    break;
            }


            Debug.Write(this.slvr.Statistics.ToString(), Debug.VERBOSE_STATS);
            //statistics = this.StatisticsToString();

            this.slvr.Pop(1);

            return ret;
        }

        public Boolean CheckEqual(Expr a, Expr b)
        {
            Controller.Instance.Z3.slvr.Push();
            Expr eq = Controller.Instance.Z3.MkEq(a, b);
            Boolean result = false;

            // only try proving equal if checking equal is satisfiable (should be faster in general)
            //if (Controller.Instance.Z3.checkTerm(eq))
            //{
            //result = Controller.Instance.Z3.proveTerm(eq);
            //}

            result = (Controller.Instance.Z3.checkTerm(eq));
            Controller.Instance.Z3.slvr.Pop();
            return result;
        }

        public Boolean ProveEqual(Expr a, Expr b)
        {
            Controller.Instance.Z3.slvr.Push();
            Expr eq = Controller.Instance.Z3.MkEq(a, b);
            Boolean result = false;

            // only try proving equal if checking equal is satisfiable (should be faster in general)
            //if (Controller.Instance.Z3.checkTerm(eq))
            //{
                result = Controller.Instance.Z3.proveTerm(eq);
            //}
            Controller.Instance.Z3.slvr.Pop();
            return result;
        }

        /**
         * Prove that a contains b (if b, then a)
         */
        public Boolean ProveContains(Expr a, Expr b)
        {
            Controller.Instance.Z3.slvr.Push();
            Boolean result = Controller.Instance.Z3.proveTerm(Controller.Instance.Z3.MkImplies((BoolExpr)b, (BoolExpr)a));
            Controller.Instance.Z3.slvr.Pop();
            return result;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="t"></param>
        /// <returns></returns>
        public Boolean proveTerm(Expr t)
        {
            Model m;
            Expr[] c;
            String s;
            return proveTerm(t, out m, out c, out s);
        }

        /**
         * Prove a term (negation is unsat)
         */
        public Boolean proveTerm(Expr t, out Model model, out Expr[] core, out String statistics)
        {
            model = null;
            core = null;

            Boolean ret = false;

            Debug.Write("Term:\n\r" + t.ToString(), Debug.VERBOSE_ALL);

            //this.slvr = this.MkSolver(); // WAY slower
            //this.slvr.Assert(this.Assumptions.ToArray());

            // save the current state of the context
            this.slvr.Push();

            this.slvr.Assert( this.MkNot((BoolExpr)t)); // proved if negation is unsat
            
            Debug.Write("\n\r\n\rAttempting to prove the following: \n\r" + this.ExprArrayToString(this.slvr.Assertions) + "\n\r\n\r", Debug.VERBOSE_TERMS);

            //switch (this.slvr.Check( this.MkNot((BoolExpr)t) ))
            switch (this.slvr.Check())
            {
                case Status.UNSATISFIABLE:
                    Debug.Write("unsat: proved claim", Debug.VERBOSE_STEPS);
                    core = slvr.UnsatCore;
                    ret = true; // proved if negation is unsat
                    break;
                case Status.UNKNOWN:
                    Debug.Write("WARNING: unknown", Debug.MINIMAL);
                    Debug.Write("Term:\n\r" + t.ToString(), Debug.MINIMAL);
                    Debug.Write("\n\r\n\r All assertions: \n\r" + this.ExprArrayToString(this.slvr.Assertions) + "\n\r\n\r", Debug.MINIMAL);
                    ret = false; // may occur semantics
                    // todo: add breakpoint back and check when this gets hit
                    break;
                case Status.SATISFIABLE:
                    model = slvr.Model;
                    Debug.Write("sat: disproved claim", Debug.VERBOSE_STEPS);
                    Debug.Write(model.ToString(), Debug.VERBOSE_ALL);
                    ret = false;
                    break;
            }

            Debug.Write(this.slvr.Statistics.ToString(), Debug.VERBOSE_STATS);
            statistics = this.slvr.Statistics.ToString();

            // restore context
            this.slvr.Pop(1);

            return ret;
        }

        /**
         * Convert an expression to CNF
         */
        public Expr ToCNF(Expr e)
        {
            Params sparams = this.MkParams();
            sparams.Add("elim_and", true);
            sparams.Add("cache-all", true);
            sparams.Add("hoist-cmul", true);
            sparams.Add("hoist-mul", true);
            sparams.Add("ite-extra-rules", true);
            sparams.Add("local-ctx", true);
            sparams.Add("pull-cheap-ite", true);


            //split-largest-clause
            Params cnfparams = this.MkParams();
            cnfparams.Add("distributivity", true);
            //Then( With(Tactic('simplify'), elim_and=True), Tactic('elim-term-ite'), Tactic('tseitin-cnf'))
            //tac2 = Then( With(Tactic('simplify'), elim_and=True), Tactic('elim-term-ite'), With(Tactic('tseitin-cnf'), distributivity=False))
            // source: http://stackoverflow.com/questions/11806626/error-tactic-failed-operator-not-supported-apply-simplifier-before-invoking/11810623#11810623
            Tactic tocnf = this.Then(this.With(this.MkTactic("simplify"), sparams), this.MkTactic("elim-uncnstr"), this.MkTactic("elim-term-ite"), this.MkTactic("ctx-solver-simplify"), this.ParAndThen(this.Repeat(this.OrElse(this.MkTactic("split-clause"), this.Skip())), this.MkTactic("propagate-ineqs")), this.With(this.MkTactic("tseitin-cnf"), cnfparams));
            //Tactic tocnf = this.Then(this.MkTactic("ctx-simplify"), this.With(this.MkTactic("simplify"), sparams), this.MkTactic("ctx-solver-simplify"), this.MkTactic("elim-term-ite"), this.ParAndThen(this.Repeat(this.OrElse(this.MkTactic("split-clause"), this.Skip())), this.MkTactic("propagate-ineqs")), this.With(this.MkTactic("tseitin-cnf"), cnfparams));
            //Tactic tocnf = this.Then(this.With(this.MkTactic("simplify"), sparams), this.MkTactic("ctx-solver-simplify"), this.MkTactic("elim-term-ite"), this.MkTactic("propagate-ineqs"), this.With(this.MkTactic("tseitin-cnf"), cnfparams));
            Goal ecnf = this.MkGoal();
            ecnf.Assert(this.AssumptionsUniversal.ToArray()); // data type assumptions
            ecnf.Assert((BoolExpr)e);
            ApplyResult result = tocnf.Apply(ecnf);
            //Expr re = this.MkOr(result.Subgoals.SelectMany(sg => sg.Formulas).ToArray()); // doesn't work
            List<BoolExpr> sgfs = new List<BoolExpr>();
            uint sgi = 0;
            foreach (var sg in result.Subgoals)
            {
                BoolExpr tmpc = this.MkAnd(sg.Formulas.ToArray());
                Model m;
                Expr[] core;
                if (!checkTerm(tmpc, out m, out core)) // remove unsats
                {
                    sgi++;
                    continue;
                }
                else
                {
                    if (tmpc.ToString().Contains("k!"))
                    {
                        Debug.Write("WARNING: conversion to DNF introduced new variables, attempting to automatically rewrite them to previous model values, but errors may occur.", Debug.MINIMAL);
                        Model conv = result.ConvertModel(sgi, m);
                        conv = conv;

                        foreach (var orig in m.Decls)
                        {
                            // found the difference, use old value
                            if (!conv.Decls.Contains(orig))
                            {
                                Debug.Write("Converting from " + orig.ToString());
                                foreach (var converted in conv.Decls)
                                {
                                    if (converted != orig && !m.Decls.Contains(converted))
                                    {
                                        //tmpc = tmpc.Substitute((Expr)orig, (Expr)converted);
                                        //FuncInterp test0 = m.FuncInterp(orig);
                                        Expr test1 = m.ConstInterp(orig);
                                        
                                        //FuncInterp test2 = conv.FuncInterp(converted);
                                        Expr test3 = conv.ConstInterp(converted);
                                        test1 = test1;
                                        test3 = test3;

                                        Expr eqc = this.MkEq(converted.Apply(), test3);
                                        Expr eqo = this.MkEq(orig.Apply(), test1);

                                        eqc = eqc;
                                        eqo = eqo;

                                        tmpc = (BoolExpr)tmpc.Substitute(eqo, eqc);
                                        tmpc = (BoolExpr)tmpc.Substitute(orig.Apply(), eqc); // could be a bit only
                                    }
                                }
                            }
                        }

                    }
                    sgfs.Add(tmpc);
                }
                sgi++;
            }
            Expr re = this.MkOr(sgfs.ToArray());
            return re; 
        }


        /**
         * Convert an expression to DNF, assuming it is in CNF
         */
        public Expr ToDNF(Expr e)
        {
            //tac3 = Then( Tactic('simplify'), Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))))
            Tactic tocnf = this.Then(this.MkTactic("simplify"), this.Repeat(this.OrElse(this.MkTactic("split-clause"), this.MkTactic("skip"))));
            Goal ecnf = this.MkGoal();
            ecnf.Assert((BoolExpr)this.ToCNF(e)); // convert to CNF first
            Expr result = this.MkAnd(tocnf.Apply(ecnf).Subgoals.SelectMany(a => a.Formulas).ToArray());
            return result;
        }

        /**
         * Convert an expression array to strings
         */
        public String ExprArrayToString(Expr[] inp)
        {
            String o = "";
            if (inp != null)
            {
                foreach (var v in inp)
                {
                    o += v.ToString() + "\n";
                }
            }
            return o;
        }

        /**
         * Print a term as an appropriately formatted string (e.g., latex, phaver, etc.)
         * 
         * Limitations: not all terms can be converted to Phaver input syntax
         */
        public String ToStringFormatted(Expr t, outmode o, bool paren = false)
        {
            if (t == null)
            {
                return "";
            }

            String s = "";
            Z3_ast_kind k = t.ASTKind;
            String tmp = "";

            switch (k)
            {
                case Z3_ast_kind.Z3_QUANTIFIER_AST:
                    {
                        Quantifier q = (Quantifier)t;

                        if (q.IsUniversal)
                        {
                            s += "\\forall ";
                        }
                        else
                        {
                            s += "\\exists";
                        }

                        int i = 0;
                        int j = (int)q.NumBound - 1;
                        Expr b = null;
                        foreach (Symbol y in q.BoundVariableNames)
                        {
                            s += y.ToString();// +"\\in ";
                            if (i < q.NumBound - 1)
                            {
                                s += ", ";
                            }
                            if (q.BoundVariableSorts[i].ToString() == "Int")
                            {
                                //s += "\\mathbb{Z}";
                                //s += "\\ID";
                            }
                            else if (q.BoundVariableSorts[i].ToString() == "Real")
                            {
                                //s += "\\mathbb{R}";
                            }
                            else{
                                //s += q.Sorts[i].ToString();
                            }
                            b = (Expr)q.Body;
                            b = b.Substitute(Controller.Instance.Z3.MkConst("#" + j.ToString(), q.BoundVariableSorts[i]), Controller.Instance.Z3.MkConst(y, q.BoundVariableSorts[i])); // TODO: REWRITE FOR Z3 4.0
                            i++;
                            j--;
                        }

                        // todo: term replace in q.Body
                        //s += " : " + this.ToStringFormatted(q.Body.GetAppArgs()[1], o); // hack to avoid printing the indexing assumption
                        if (b.Args.Length >= 2)
                        {
                            s += " : ";
                            if (paren)
                            {
                                s += "(";
                            }
                            s += this.ToStringFormatted(b.Args[1], o, paren);
                            if (paren)
                            {
                                s += ")"; // todo: parenthesis based on arg
                            }
                        }
                        break;
                    }
                case Z3_ast_kind.Z3_NUMERAL_AST:
                    {
                        s += t.ToString();
                        break;
                    }
                case Z3_ast_kind.Z3_VAR_AST:
                    {
                        s += t.ToString();
                        break;
                    }
                case Z3_ast_kind.Z3_APP_AST:
                    {
                        Expr[] args = t.Args;

                        if (args != null)
                        {
                            if (args.Length == 0) // nullary (constants, etc.)
                            {
                                s += t.FuncDecl.Name.ToString();
                            }
                            else if (args.Length == 1) // unary (but have to avoid some weird types)
                            {
                                //s += this.DeclKindToStringLatex(dk);
                                switch (((uint)t.FuncDecl.DeclKind))
                                {
                                    case (uint)Z3_decl_kind.Z3_OP_UNINTERPRETED:
                                        {
                                            //System.Console.WriteLine("UNINTERP 1: " + t);
                                            //System.Console.WriteLine("UNINTERP 1 func: " + t.FuncDecl);
                                            //System.Console.WriteLine("UNINTERP 1 name: " + t.FuncDecl.Name);
                                            tmp = t.FuncDecl.Name.ToString();
                                            tmp += "[" + this.ToStringFormatted(args[0], o, paren) + "]"; // we do a string replace using brackets for phaver output
                                            // todo: check generality
                                            if (tmp.Contains(Controller.PRIME_SUFFIX))
                                            {
                                                tmp = tmp.Replace(Controller.PRIME_SUFFIX, "");
                                                tmp += Controller.PRIME_SUFFIX;
                                            }
                                            s += tmp;
                                            break;
                                        }
                                    case (uint)Z3_decl_kind.Z3_OP_NOT:
                                    case (uint)Z3_decl_kind.Z3_OP_BNEG:
                                        {
                                            switch (o)
                                            {
                                                case outmode.MODE_PHAVER:
                                                    {
                                                        s += " ! ";
                                                        if (paren)
                                                        {
                                                            s += "(";
                                                        }
                                                        s += this.ToStringFormatted(args[0], o, paren);
                                                        if (paren)
                                                        {
                                                            s += ")";
                                                        }
                                                        break;
                                                    }
                                                case outmode.MODE_LATEX: // pass through
                                                default:
                                                    {
                                                        s += " \\neg";
                                                        if (paren)
                                                        {
                                                            s += "(";
                                                        }
                                                        s += this.ToStringFormatted(args[0], o, paren);
                                                        if (paren)
                                                        {
                                                            s += ")";
                                                        }
                                                        break;
                                                    }
                                            }
                                            break;
                                        }
                                    case (uint)Z3_decl_kind.Z3_OP_SET_DIFFERENCE:
                                    case (uint)Z3_decl_kind.Z3_OP_UMINUS:
                                    case (uint)Z3_decl_kind.Z3_OP_SUB:
                                        {
                                            s += " - (" + this.ToStringFormatted(args[0], o, paren) + ")";
                                            break;
                                        }
                                    default:
                                        {
                                            // matches a variable name
                                            // TODO: generality
                                            //if (Controller.Instance.Sys.Variables.Any(v => v.Name == t.FuncDecl.Name.ToString())) // (not indexed, globals...)
                                            if (Controller.Instance.Sys.HybridAutomata[0].Variables.Any(v => v.Name == t.FuncDecl.Name.ToString().Replace(Controller.PRIME_SUFFIX, ""))) // indexed variables
                                            {
                                                tmp = t.FuncDecl.Name.ToString();
                                                tmp += "[" + this.ToStringFormatted(args[0], o, paren) + "]"; // we do a string replace using brackets for phaver output
                                                if (tmp.Contains(Controller.PRIME_SUFFIX))
                                                {
                                                    tmp = tmp.Replace(Controller.PRIME_SUFFIX, "");
                                                    tmp += Controller.PRIME_SUFFIX;
                                                }
                                                s += tmp;
                                            }
                                            // not a variable
                                            else
                                            {
                                                s += this.ToStringFormatted(args[0], o, paren);
                                            }
                                            break;
                                        }
                                }

                            }
                            else if (args.Length >= 2)
                            {
                                //System.Console.WriteLine("UNINTERP 2: " + t);
                                //System.Console.WriteLine("UNINTERP 2 func: " + t.FuncDecl);
                                //System.Console.WriteLine("UNINTERP 2 name: " + t.FuncDecl.Name);
                                uint i = 0;
                                while (i < args.Length)
                                {
                                    // hack to detect location to print the mode name if it exists
                                    if (i > 0 && s.Contains("q[") && args[i - 1].ToString().StartsWith("(q"))
                                    {
                                        s += Controller.Instance.LocationNumTermToName[args[i]];
                                    }
                                    else
                                    {
                                        if (args[i].NumArgs > 1 && paren)
                                        {
                                            s += "(" + this.ToStringFormatted(args[i], o, paren) + ")";
                                        }
                                        else
                                        {
                                            s += this.ToStringFormatted(args[i], o, paren);
                                        }
                                    }

                                    if (i < args.Length - 1)
                                    {
                                        s += this.DeclKindToString(t.FuncDecl.DeclKind, o);
                                    }
                                    i++;
                                }
                            }
                        }
                        break;
                    }
            }
            return s;
        }

        /**
         * Convert a declaration kind to string
         */
        public String DeclKindToString(Z3_decl_kind dk, outmode o)
        {
            String s = "";
            switch (dk)
            {
                case Z3_decl_kind.Z3_OP_ADD:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                        case outmode.MODE_PHAVER:
                            {
                                s += " + ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " + ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_AND:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                            {
                                s += " &amp; ";
                                break;
                            }
                        case outmode.MODE_PHAVER:
                            {
                                s += " & ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\wedge ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_RA_COMPLEMENT: // TODO: check
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " ! ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\not ";
                                break;
                            }
                    }
                    
                    break;
                case Z3_decl_kind.Z3_OP_SET_DIFFERENCE:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " - "; // TODO: no equivalent
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\setminus ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_DISTINCT: // TODO:
                    s += "distinct ";
                    break;
                case Z3_decl_kind.Z3_OP_DIV:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                        case outmode.MODE_PHAVER:
                            {
                                s += " / ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " / ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_EQ:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                        case outmode.MODE_PHAVER:
                            {
                                s += " == ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " = ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_BNEG:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " != ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \neq ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_FALSE:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " false ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\false ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_GE:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                            {
                                s += " &gt;= ";
                                break;
                            }
                        case outmode.MODE_PHAVER:
                            {
                                s += " >= ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\geq ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_GT:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                            {
                                s += " &gt; ";
                                break;
                            }
                        case outmode.MODE_PHAVER:
                            {
                                s += " > ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " > ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_IFF:
                    s += " \\Leftrightarrow ";
                    break;
                case Z3_decl_kind.Z3_OP_IMPLIES:
                    s += " \\Rightarrow ";
                    break;
                case Z3_decl_kind.Z3_OP_SET_INTERSECT:
                    s += " \\cap ";
                    break;
                case Z3_decl_kind.Z3_OP_ITE:
                    s += " ite ";
                    break;
                case Z3_decl_kind.Z3_OP_LE:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                            {
                                s += " &lt;= ";
                                break;
                            }
                        case outmode.MODE_PHAVER:
                            {
                                s += " <= ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\leq ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_LT:
                    switch (o)
                    {
                        case outmode.MODE_SPACEEX:
                            {
                                s += " &lt; ";
                                break;
                            }
                        case outmode.MODE_PHAVER:
                            {
                                s += " < ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " < ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_MOD:
                case Z3_decl_kind.Z3_OP_MUL:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " * ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " * ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_NOT:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " ! ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\neg ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_OR:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " | ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\vee ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_REM:
                    break;
                case Z3_decl_kind.Z3_OP_SUB:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " - ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " - ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_SET_SUBSET:
                    s += " \\subset ";
                    break;
                case Z3_decl_kind.Z3_OP_TRUE:
                    switch (o)
                    {
                        case outmode.MODE_PHAVER:
                            {
                                s += " true ";
                                break;
                            }
                        case outmode.MODE_LATEX: // pass through
                        default:
                            {
                                s += " \\true ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_UMINUS:
                    s += " - ";
                    break;
                case Z3_decl_kind.Z3_OP_SET_UNION:
                    s += " \\cup ";
                    break;
                case Z3_decl_kind.Z3_OP_XOR:
                    break;
                default:
                    break;
            }
            return s;
        }

        /**
         * Check an array of terms
         */
        /*
        public Boolean checkTerms(Expr[] t)
        {
            Boolean debug = false;
            Boolean ret = false;

            if (debug)
            {
                Console.WriteLine("Term:\n\r" + t[0].ToString());
                Console.WriteLine("Term:\n\r" + t[1].ToString());
            }

            this.slvr.Push();

            this.slvr.Assert(t[0]);
            this.slvr.Assert(t[1]);
            //this._z3.AssertCnstr(this._z3.MkNot(t));

            //Term not_f = this._z3.MkNot(guard);
            //this._z3.AssertCnstr(not_f);

            Model model = null;
            switch (this.slvr.Check(out model))
            {
                case LBool.False:
                    if (debug)
                    {
                        Console.WriteLine("unsat");
                    }
                    ret = false;
                    break;
                case LBool.Undef:
                    if (debug)
                    {
                        Console.WriteLine("unknown");
                    }
                    ret = true; // may occur semantics
                    break;
                case LBool.True:
                    if (debug)
                    {
                        Console.WriteLine("sat");
                        model.Display(Console.Out);
                    }
                    ret = true;
                    break;
            }
            if (model != null)
            {
                model.Dispose();
            }

            if (debug)
            {
                this.DisplayStatistics(Console.Out);
            }

            this.Pop(1);

            return ret;
        }
*/
    }
}
