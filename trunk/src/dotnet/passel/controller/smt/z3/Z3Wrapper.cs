using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.model;

using passel.controller;
using System.Text.RegularExpressions;

namespace passel.controller.smt.z3
{
    public class Z3Wrapper : Microsoft.Z3.Context
    {
        public enum PrintFormatMode { latex, phaver };

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
            p.Add("pull-nested-quantifiers", true);
            Tactic tsimplify = this.With(this.MkTactic("simplify"), p);
            tsimplify = this.OrElse(tsimplify, this.MkTactic("skip"));

            p = this.MkParams();
            p.Add("qe-nonlinear", true);
            Tactic tqe = this.With(this.MkTactic("qe"), p);
            tqe = this.OrElse(tqe, this.MkTactic("skip"));

            //p = this.MkParams();
            //Tactic tfm = this.With(this.MkTactic("fm"), p);
            //tfm = this.OrElse(tfm, this.MkTactic("skip"));

            p = this.MkParams();
            //p.Add("pull-cheap-ite", true);
            Tactic tctxsimplify = this.With(this.MkTactic("ctx-simplify"), p);
            tctxsimplify = this.OrElse(tctxsimplify, this.MkTactic("skip"));

            p = this.MkParams();
            Tactic tpreprocess = this.MkTactic("sat-preprocess");
            tpreprocess = this.OrElse(tpreprocess, this.MkTactic("skip"));

            // some bug with distribute-forall, all become false
            p = this.MkParams();
            //Tactic tdistributeForall = this.MkTactic("distribute-forall"); // all false
            string[] alltactics = TacticNames;
            //Tactic tdistributeForall = this.MkTactic("add-bounds"); // all false
            //Tactic tdistributeForall = this.MkTactic("qfnra");
            //Tactic tdistributeForall = this.MkTactic("qflra"); 

            string[] ts = { "nlsat", "split-clause", "der", "normalize-bounds", "qfnra", "qflra", "symmetry-reduce", "qfnia", "qflia", "diff-neq", "purify-arith", "max-bv-sharing", "elim-term-ite", "propagate-values", "elim-and", "elim-uncnstr" };
            //string[] ts = { "nlsat", "qe-sat", "split-clause", "der", "normalize-bounds", "qfnra", "qflra", "symmetry-reduce", "qfnia", "qflia", "diff-neq", "purify-arith", "max-bv-sharing", "elim-term-ite", "propagate-values", "elim-and", "elim-uncnstr" };

            //string[] ts = { "nlsat", "qe-sat", "diff-neq", "purify-arith" };
            //string[] ts = { "nlsat", "qe-sat" };
            //string[] ts = {  "qe-sat" };

            List<Tactic> lts = new List<Tactic>();
            foreach (var a in ts)
            {
                lts.Add(this.OrElse(this.MkTactic(a), this.MkTactic("skip")));
            }

            //tdistributeForall = this.OrElse(tdistributeForall, this.MkTactic("skip"));

            p = this.MkParams();
            Tactic tvsubst = this.MkTactic("vsubst");
            tvsubst = this.OrElse(tvsubst, this.MkTactic("skip"));

            p = this.MkParams();
            p.Add("produce-models", true);
            p.Add("candidate-models", true);
            p.Add("mbqi", true);
            p.Add("auto-config", false);
            p.Add("ematching", true);
            p.Add("pull-nested-quantifiers", true);

            p.Add("hi-div0", true);
            p.Add("relevancy", true);
            p.Add("qi-eager-threshold", 1000);
            p.Add("qi-lazy-threshold", 1000);

            //pull-nested-quantifiers
            Tactic tsmt = this.With(this.MkTactic("smt"), p);
            //tsmt = this.OrElse(tsmt, this.MkTactic("skip"));

            //t = this.Repeat(this.ParOr(tqe, tsmt));
            //t = this.With(this.Repeat(this.Then(tqe, tsmt)), p);


            p = this.MkParams();
            p.Add("produce-models", true);
            p.Add("candidate-models", true);
            p.Add("mbqi", true);
            p.Add("auto-config", false);
            p.Add("ematching", true);
            p.Add("pull-nested-quantifiers", true);


            //t = this.With(this.Repeat(this.Then(tsimplify, tctxsimplify, tdistributeForall, tpreprocess, tqe, tvsubst, tsmt)), p);
            lts.AddRange(new Tactic[] {tsimplify, tctxsimplify, tpreprocess, tqe, tvsubst, tsmt});
            Tactic[] tsmore = lts.GetRange(2, lts.Count - 2).ToArray();
            t = this.With(this.Repeat(this.Then(lts[0], lts[1], tsmore)), p);
            

            //this.slvr = t.Solver;


            /*
             * NOTES: 2012/11/27
             * 
             * Previously, we had been using this.MkSolver(), which would return a default solver with the appropriate tactics as specified by global configuration parameters.
             * However, more recent versions of Z3 have disabled some of these (particularly the ELIM_QUANT option), which caused problems for some transitions.
             * 
             * The key solvers appear to be: smt, qe, and qe-sat
             */

            this.slvr = this.MkSolver(t);

            System.Console.WriteLine("Custom tactic options:");
            System.Console.WriteLine(this.slvr.Help);
            //System.Console.WriteLine(this.slvr.ParameterDescriptions);
            
            this.slvr = this.MkSolver(); // (par-or smt qe)
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
            if (orig != null)
            {
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

        /**
         * abstract global indexed variables
         */
        public Expr abstractGlobals(Expr f, uint N, uint projectN, uint i, uint j)
        {
            // TODO: SPECIAL CARE MUST BE TAKEN DEFINITELY FOR INDEX-VALUED GLOBAL VARIABLES, AND POSSIBLY ALSO FOR INDEXED CONTROL LOCATION VARIABLES....

            System.Console.WriteLine("Property before generalization: ");
            System.Console.WriteLine(f.ToString() + "\n\r\n\r");

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

            System.Console.WriteLine("Property after generalization: ");
            System.Console.WriteLine(f.ToString() + "\n\r\n\r");

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
                                    if (varname == "q")
                                    {
                                        origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.Q[sidx]);
                                    }
                                    else
                                    {
                                        origReplaced = origReplaced.Substitute(v.Value, Controller.Instance.IndexedVariables[kv]);
                                    }
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
         */
        public void unprimeAllVariables(ref Expr origReplaced, int k)
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
                            FuncDecl preState = Controller.Instance.Z3.MkFuncDecl(v.Key + (k-1).ToString(), v.Value.Domain, v.Value.Range);
                            replaceFuncDecl(ref origReplaced, origReplaced, v.Value, preState, false);
                        }
                        // replace primed by post-state index (todo: merge with previous loop)
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDeclPrimed)
                        {
                            FuncDecl postState = Controller.Instance.Z3.MkFuncDecl(v.Key + k.ToString(), v.Value.Domain, v.Value.Range);
                            replaceFuncDecl(ref origReplaced, origReplaced, v.Value, postState, false);
                        }
                        break;
                    }
            }

            foreach (var v in Controller.Instance.GlobalVariables) // uses primed from earlier revision before global variables added in more coherent manner (were parameters with update_type)
            {
                Expr preState = Controller.Instance.Z3.MkConst(v.Key + (k-1).ToString(), v.Value.Sort); // todo: make sure constructed as appropriately typed sorts, not uninterpreted...
                Expr postState = Controller.Instance.Z3.MkConst(v.Key + k.ToString(), v.Value.Sort);
                origReplaced = origReplaced.Substitute(v.Value, preState);
                origReplaced = origReplaced.Substitute(Controller.Instance.GlobalVariablesPrimed[v.Key], postState);
            }
        }

        /**
         * Distinct terms
         */
        public Expr MkDistinct(Expr t1, Expr t2)
        {
            return this.MkDistinct(new Expr[] { t1, t2 });
        }

        /**
         * Identity function for all processes not making a transition
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         */
        public Expr forallIdentity(Expr indexMakingMove, List<String> globalVariableResets, List<String> indexVariableResets, List<String> universalIndexVariableResets, Expr uguardReset)
        {
            List<BoolExpr> f = new List<BoolExpr>();
            List<BoolExpr> outside_forall = new List<BoolExpr>();
            List<Expr> bound = new List<Expr>();
            String idx = "j";

            bound.Add(Controller.Instance.Indices[idx]);

            // set equality on unprimed pre-state and primed post-state for all indexed variables of all other processes (those not making the move) (e.g., q[j]' == q[j])
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            if (!universalIndexVariableResets.Contains(v.Key))
                            {
                                //grab only idx
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));
                            }
                            else
                            {
                                if (uguardReset != null)
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (universalIndexVariableResets != null && !universalIndexVariableResets.Contains(v.Key))
                            {
                                //grab only idx
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));

                                // add basic universal guard
                                // TODO: CHECK IF THIS WORKS WITH RESETS
                                if (uguardReset != null && !uguardReset.ToString().Contains(Controller.PRIME_SUFFIX) && !uguardReset.ToString().Contains(Controller.PRIME_SUFFIX_PARSER))
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                            else
                            {
                                if (uguardReset != null)
                                {
                                    f.Add((BoolExpr)uguardReset);
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all unprimed pre-state and primed post-state of all indexed variables ***NOT APPEARING IN THE RESET*** for the process making the move (e.g., x[h]' == x[h], if x[h] is not reset)
            if (indexMakingMove != null)
            {
                if (indexVariableResets != null)
                {
                    foreach (var v in indexVariableResets)
                    {
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v], indexMakingMove)));
                                    break;
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v], indexMakingMove)));
                                    break;
                                }
                        }
                    }
                }
            }

            if (globalVariableResets != null)
            {
                // set equality on all unprimed pre-state and primed post-tate of all global variables ***NOT APPEARING IN THE RESET*** (e.g., g' == g, if g is not reset)
                foreach (var v in globalVariableResets)
                {
                    outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v], Controller.Instance.GlobalVariablesPrimed[v]));
                }
            }
            List<BoolExpr> ibds = new List<BoolExpr>();
            if (Controller.Instance.IndexOption == Controller.IndexOptionType.naturalOneToN)
            {
                ibds.Add(this.MkGe((ArithExpr)Controller.Instance.Indices[idx], (ArithExpr)Controller.Instance.IndexOne));
                ibds.Add(this.MkLe((ArithExpr)Controller.Instance.Indices[idx], (ArithExpr)Controller.Instance.IndexN));
            }

            Expr ret;
            Expr fand = Controller.Instance.Z3.MkAnd(f.ToArray());
            if (indexMakingMove != null)
            {
                Expr distinct = Controller.Instance.Z3.MkDistinct(bound.First(), indexMakingMove);

                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.integer:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies((BoolExpr)distinct, (BoolExpr)fand)); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                    case Controller.IndexOptionType.naturalOneToN:
                        ibds.Add((BoolExpr)distinct);
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd(ibds.ToArray()), (BoolExpr)fand)); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                    case Controller.IndexOptionType.enumeration:
                    default:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies((BoolExpr)distinct, (BoolExpr)fand)); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                }
            }
            else
            {
                switch (Controller.Instance.IndexOption)
                {
                    case Controller.IndexOptionType.integer:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), fand); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                    case Controller.IndexOptionType.naturalOneToN:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd((BoolExpr[])ibds.ToArray()), (BoolExpr)fand)); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                    case Controller.IndexOptionType.enumeration:
                    default:
                        ret = Controller.Instance.Z3.MkForall(bound.ToArray(), fand); // todo: check order of this distinct...in antecedent or consequent?
                        break;
                }
            }

            // only add the outside forall constraints if there are any
            if (outside_forall.Count > 0)
            {
                outside_forall.Add((BoolExpr)ret); // prettier printing (fewer ands)
                ret = Controller.Instance.Z3.MkAnd(outside_forall.ToArray());
            }
            return ret;
        }

        /**
         * Identity function for all non-continuous variables
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         * 
         * indexForall is the name of the universally quantified index
         */
        public Expr timeIdentity(Expr indexForall)
        {
            List<BoolExpr> f = new List<BoolExpr>();

            // set equality on all non-clock variables
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                    {
                        foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, indexForall), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType != Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, indexForall), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType != Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all global variables
            foreach (var v in Controller.Instance.Sys.Variables)
            {
                if (v.UpdateType != Variable.VarUpdateType.continuous)
                {
                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.GlobalVariablesPrimed[v.Name]));
                }
            }

            if (f.Count > 1)
            {
                return Controller.Instance.Z3.MkAnd(f.ToArray());
            }
            else if (f.Count == 1)
            {
                return f[0];
            }
            else
            {
                return Controller.Instance.Z3.MkTrue();
            }
        }

        /**
         * Identity function for all continuous variables
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         * 
         * indexForall is the name of the universally quantified index
         */
        public Expr timeNoFlowIdentity(Expr indexForall)
        {
            List<BoolExpr> f = new List<BoolExpr>();

            // set equality on all non-clock variables
            switch (Controller.Instance.DataOption)
            {
                case Controller.DataOptionType.array:
                        {
                            foreach (var v in Controller.Instance.DataA.IndexedVariableDecl)
                            {
                                if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                                {
                                    continue;
                                }
                                foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                                {
                                    if (ha.GetVariableByName(v.Key).UpdateType == Variable.VarUpdateType.continuous)
                                    {
                                        //grab only the universally quantified one
                                        f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkSelect(v.Value, indexForall), Controller.Instance.Z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                    }
                                }
                            }
                            break;
                        }
                case Controller.DataOptionType.uninterpreted_function:
                default:
                    {
                        foreach (var v in Controller.Instance.DataU.IndexedVariableDecl)
                        {
                            if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                            {
                                continue;
                            }
                            foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                            {
                                if (ha.GetVariableByName(v.Key).UpdateType == Variable.VarUpdateType.continuous)
                                {
                                    //grab only the universally quantified one
                                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[v.Key], indexForall)));
                                }
                            }
                        }
                        break;
                    }
            }

            // set equality on all global variables
            foreach (var v in Controller.Instance.Sys.Variables)
            {
                if (v.UpdateType == Variable.VarUpdateType.continuous)
                {
                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.GlobalVariables[v.Name], Controller.Instance.GlobalVariablesPrimed[v.Name]));
                }
            }

            if (f.Count > 1)
            {
                return Controller.Instance.Z3.MkAnd(f.ToArray());
            }
            else if (f.Count == 1)
            {
                return f[0];
            }
            else{
                return Controller.Instance.Z3.MkTrue();
            }
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


        /**
         * Check a term
         */
        public Boolean checkTerm(Expr t, out Model model, out Expr[] core, params Boolean[] options)
        {
            model = null;
            core = null;
            Boolean debug = false;
            try
            {
                debug = options[0];
            }
            catch
            {
            }
            Boolean ret = false;

            if (debug)
            {
                //Console.WriteLine("Term:\n\r" + t.ToString());
            }
            //Console.WriteLine("Term:\n\r" + t.ToString());

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
                    if (debug)
                    {
                        Console.WriteLine("unsat");
                    }
                    ret = false;
                    core = slvr.UnsatCore;
                    break;
                case Status.UNKNOWN:
                    if (debug)
                    {
                        Console.WriteLine("unknown");
                        Console.WriteLine("Term:\n\r" + t.ToString());
                    }
                    ret = true; // may occur semantics
                    break;
                case Status.SATISFIABLE:
                    if (debug)
                    {
                        Console.WriteLine("sat");
                        //Console.WriteLine(slvr.Model.ToString());
                    }
                    ret = true;
                    model = slvr.Model;
                    break;
            }

            if (debug)
            {
                Console.WriteLine(this.slvr.Statistics.ToString());
            }
            //statistics = this.StatisticsToString();

            this.slvr.Pop(1);

            return ret;
        }

        /**
         * Prove a term (negation is unsat)
         */
        public Boolean proveTerm(Expr t, out Model model, out Expr[] core, out String statistics, params Boolean[] options)
        {
            model = null;
            core = null;
            Boolean debug = false;
            try
            {
                debug = options[0];
            }
            catch
            {
            }
            Boolean ret = false;

            if (debug)
            {
                //Console.WriteLine("Term:\n\r" + t.ToString());
            }

            //this.slvr = this.MkSolver(); // WAY slower
            //this.slvr.Assert(this.Assumptions.ToArray());

            // save the current state of the context
            this.slvr.Push();

            this.slvr.Assert( this.MkNot((BoolExpr)t)); // proved if negation is unsat
            
            Console.WriteLine("\n\r\n\rAttempting to prove the following: \n\r" + this.ExprArrayToString(this.slvr.Assertions) + "\n\r\n\r");

            //switch (this.slvr.Check( this.MkNot((BoolExpr)t) ))
            switch (this.slvr.Check())
            {
                case Status.UNSATISFIABLE:
                    if (debug)
                    {
                        Console.WriteLine("unsat: proved claim");
                    }
                    core = slvr.UnsatCore;
                    ret = true; // proved if negation is unsat
                    break;
                case Status.UNKNOWN:
                    if (debug)
                    {
                        Console.WriteLine("unknown: quantifier elimination failure");
                        Console.WriteLine("Term:\n\r" + t.ToString());
                        Console.WriteLine("\n\r\n\r All assertions: \n\r" + this.ExprArrayToString(this.slvr.Assertions) + "\n\r\n\r");
                    }
                    ret = false; // may occur semantics
                    // todo: add breakpoint back and check when this gets hit
                    break;
                case Status.SATISFIABLE:
                    model = slvr.Model;
                    if (debug)
                    {
                        Console.WriteLine("sat: disproved claim");
                        //Console.WriteLine(model.ToString());
                    }
                    ret = false;
                    break;
            }

            if (debug)
            {
                Console.WriteLine(this.slvr.Statistics.ToString());
            }
            statistics = this.slvr.Statistics.ToString();

            // restore context
            this.slvr.Pop(1);

            return ret;
        }

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
         * Print a term as a latex string
         */
        
        public String ToStringFormatted(Expr t, PrintFormatMode o, bool paren = false)
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
                            Z3_decl_kind dk = t.FuncDecl.DeclKind;
                            if (args.Length == 0) // nullary (constants, etc.)
                            {
                                s += t.FuncDecl.Name.ToString();
                            }
                            else if (args.Length == 1) // unary (but have to avoid some weird types)
                            {
                                //s += this.DeclKindToStringLatex(dk);
                                switch (dk)
                                {
                                    case Z3_decl_kind.Z3_OP_UNINTERPRETED:
                                        {
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
                                    case Z3_decl_kind.Z3_OP_NOT:
                                    case Z3_decl_kind.Z3_OP_BNEG:
                                        {
                                            switch (o)
                                            {
                                                case PrintFormatMode.phaver:
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
                                                case PrintFormatMode.latex: // pass through
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
                                    case Z3_decl_kind.Z3_OP_SET_DIFFERENCE:
                                    case Z3_decl_kind.Z3_OP_UMINUS:
                                    case Z3_decl_kind.Z3_OP_SUB:
                                        {
                                            s += " - (" + this.ToStringFormatted(args[0], o, paren) + ")";
                                            break;
                                        }
                                    default:
                                        {
                                            s += this.ToStringFormatted(args[0], o, paren);
                                            break;
                                        }
                                }

                            }
                            else if (args.Length >= 2)
                            {
                                uint i = 0;
                                while (i < args.Length)
                                {
                                    // hack to detect location to print the mode name if it exists
                                    if (i > 0 && s.Contains("q[") && args[i - 1].ToString().StartsWith("(q"))
                                    {
                                        // only display first letter of location in caps (e.g., for SATS)
                                        //s += Controller.Instance.LocationNumTermToName[args[i]].Substring(0,1).ToUpper(); // todo: add error handling (buggy with bitvectors)
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
                                        s += this.DeclKindToString(dk, o);
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
        public String DeclKindToString(Z3_decl_kind dk, PrintFormatMode o)
        {
            String s = "";
            switch (dk)
            {
                case Z3_decl_kind.Z3_OP_ADD:
                    switch (o)
                    {
                        case PrintFormatMode.phaver:
                            {
                                s += " + ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " & ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " ! ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " - "; // TODO: no equivalent
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
                        default:
                            {
                                s += " \\setminus ";
                                break;
                            }
                    }
                    break;
                case Z3_decl_kind.Z3_OP_DISTINCT:
                    break;
                case Z3_decl_kind.Z3_OP_DIV:
                    switch (o)
                    {
                        case PrintFormatMode.phaver:
                            {
                                s += " / ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " == ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " != ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " false ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " >= ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " > ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " <= ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " < ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " * ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " ! ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " | ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " - ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
                        case PrintFormatMode.phaver:
                            {
                                s += " true ";
                                break;
                            }
                        case PrintFormatMode.latex: // pass through
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
