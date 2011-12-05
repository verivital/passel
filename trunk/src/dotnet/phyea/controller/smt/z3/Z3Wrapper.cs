using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.model;

namespace phyea.controller.smt.z3
{
    public class Z3Wrapper : Microsoft.Z3.Context
    {
        public Z3Wrapper(Config c) :
            base(c)
        {
        }

        /**
        * Replace all references to a function declaration in a tree of terms
        */
        public void replaceFuncDecl(ref Term origReplaced, Term orig, FuncDecl find, FuncDecl replace, Boolean byString)
        {
            if (orig != null)
            {
                if (orig.GetKind() == TermKind.App && orig.GetAppDecl().Equals(find) || (byString && orig.ToString().Equals(find.ToString())))
                {
                    origReplaced = Controller.Instance.Z3.MkApp(replace, orig.GetAppArgs());
                    //return;
                }
                try
                {
                    Term[] ts;

                    switch (orig.GetKind())
                    {
                        case TermKind.Quantifier:
                            Symbol[] n = orig.GetQuantifier().Names;
                            ts = new Term[] { orig.GetQuantifier().Body };
                            break;
                        case TermKind.App:
                            FuncDecl fd = orig.GetAppDecl(); // todo: do the replacement on this---make another function do this replacement only for priming and unpriming (will be much faster)
                            ts = orig.GetAppArgs();
                            break;
                        case TermKind.Numeral: // bottom of tree
                            return;
                        case TermKind.Var:
                            return;
                        default:
                            return;
                    }

                    for (int i = 0; i < ts.Length; i++)
                    {
                        replaceFuncDecl(ref ts[i], ts[i], find, replace, byString);
                    }
                    // call term modifier from api

                    if (origReplaced.GetKind() == TermKind.Quantifier)
                    {
                        Symbol[] n = orig.GetQuantifier().Names;
                        origReplaced = this.UpdateTerm(origReplaced, ts);
                    }
                    else
                    {
                        origReplaced = this.UpdateTerm(origReplaced, ts);
                    }
                }
                catch (Microsoft.Z3.Z3Error e)
                {
                }
            }
        }

        /**
         * Find all global variables that are primed in the reset and exclude them from the identity for transitions
         */
        public List<String> findGlobalVariableResets(Term reset)
        {
            List<String> vars = new List<String>();

            foreach (var v in Controller.Instance.ParamsPrimed)
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
        public List<String> findIndexedVariableResets(Term reset)
        {
            List<String> vars = new List<String>();

            foreach (var v in Controller.Instance.IndexedVariableDeclPrimed)
            {
                if (!v.Key.Contains("q") && !this.findFunc(reset, v.Key, false))
                {
                    vars.Add(v.Key);
                }
            }
            return vars;
        }

        /**
         * Determine whether a particular function declaration appears in a tree of terms
         */
        public Boolean findFunc(Term haystack, String needle, Boolean byString)
        {
            // todo: horrible hack: just search by string
            if (haystack == null)
            {
                return false;
            }
            else
            {
                String t1 = haystack.ToString();
                return (haystack.ToString().Contains(needle + "'"));
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
        public Boolean findTerm(Term haystack, Term needle, Boolean byString)
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
         * Prime all variables
         */
        public void primeAllVariables(ref Term origReplaced)
        {
            foreach (var v in Controller.Instance.IndexedVariableDecl)
            {
                replaceFuncDecl(ref origReplaced, origReplaced, v.Value, Controller.Instance.IndexedVariableDeclPrimed[v.Key], false);
            }

            foreach (var v in Controller.Instance.ParamsPrimed)
            {
                replaceTerm(ref origReplaced, origReplaced, Controller.Instance.Params[v.Key], v.Value, false);
            }
        }

        /**
         * Distinct terms
         */
        public Term MkDistinct(Term t1, Term t2)
        {
            return this.MkDistinct(new Term[] { t1, t2 });
        }

        /**
         * Identity function for all processes not making a transition
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         */
        public Term forallIdentity(Term indexMakingMove, List<String> globalVariableResets, List<String> indexVariableResets)
        {
            List<Term> f = new List<Term>();
            List<Term> outside_forall = new List<Term>();
            List<Term> bound = new List<Term>();
            String idx = "j";

            bound.Add(Controller.Instance.Indices[idx]);

            // set equality on unprimed pre-state and primed post-state for all indexed variables of all other processes (those not making the move) (e.g., q[j]' == q[j])
            foreach (var v in Controller.Instance.IndexedVariableDecl)
            {
                //grab only idx
                f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, Controller.Instance.Indices[idx]), Controller.Instance.Z3.MkApp(Controller.Instance.IndexedVariableDeclPrimed[v.Key], Controller.Instance.Indices[idx])));
            }

            // set equality on all unprimed pre-state and primed post-state of all indexed variables ***NOT APPEARING IN THE RESET*** for the process making the move (e.g., x[h]' == x[h], if x[h] is not reset)
            foreach (var v in indexVariableResets)
            {
                outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(Controller.Instance.IndexedVariableDecl[v], indexMakingMove), Controller.Instance.Z3.MkApp(Controller.Instance.IndexedVariableDeclPrimed[v], indexMakingMove)));
            }

            // set equality on all unprimed pre-state and primed post-tate of all global variables ***NOT APPEARING IN THE RESET*** (e.g., g' == g, if g is not reset)
            foreach (var v in globalVariableResets)
            {
                outside_forall.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Params[v], Controller.Instance.ParamsPrimed[v]));
            }
            List<Term> ibds = new List<Term>();
            ibds.Add(Controller.Instance.Indices[idx] >= Controller.Instance.IntOne);
            ibds.Add(Controller.Instance.Indices[idx] <= Controller.Instance.N);
            //return Controller.Instance.Z3.MkAnd(outside_forall.ToArray()) & Controller.Instance.Z3.MkForall(0, bound.ToArray(), null, Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd(ibds.ToArray()) & Controller.Instance.Z3.MkDistinct(bound.First(), indexMakingMove), Controller.Instance.Z3.MkAnd(f.ToArray()))); // todo: check order of this distinct...in antecedent or consequent?
            return Controller.Instance.Z3.MkAnd(outside_forall.ToArray()) & Controller.Instance.Z3.MkForall(0, bound.ToArray(), null, Controller.Instance.Z3.MkImplies( Controller.Instance.Z3.MkImplies(Controller.Instance.Z3.MkAnd(ibds.ToArray()), Controller.Instance.Z3.MkDistinct(bound.First(), indexMakingMove)), Controller.Instance.Z3.MkAnd(f.ToArray()))); // todo: check order of this distinct...in antecedent or consequent?
        }

        /**
         * Identity function for all non-continuous variables
         * I.e., forall j \neq i . q[j]' = q[j] /\ \ldots /\ g' = g, if global var g is not modified in transition of i
         * 
         * indexForall is the name of the universally quantified index
         */
        public Term timeIdentity(Term indexForall)
        {
            List<Term> f = new List<Term>();

            // set equality on all non-clock variables
            foreach (var v in Controller.Instance.IndexedVariableDecl)
            {
                if (v.Key.Equals("Q", StringComparison.InvariantCultureIgnoreCase))
                {
                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.IndexedVariableDeclPrimed[v.Key], indexForall)));
                    continue;
                }
                foreach (var ha in Controller.Instance.Sys.HybridAutomata)
                {
                    if (ha.GetVariableByName(v.Key).UpdateType != AVariable.VarUpdateType.continuous)
                    {
                        //grab only the universally quantified one
                        f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Z3.MkApp(v.Value, indexForall), Controller.Instance.Z3.MkApp(Controller.Instance.IndexedVariableDeclPrimed[v.Key], indexForall)));
                    }
                }
            }

            // set equality on all global variables
            foreach (var v in Controller.Instance.Sys.Variables)
            {
                if (v.UpdateType != AVariable.VarUpdateType.continuous)
                {
                    f.Add(Controller.Instance.Z3.MkEq(Controller.Instance.Params[v.Name], Controller.Instance.ParamsPrimed[v.Name]));
                }
            }

            return Controller.Instance.Z3.MkAnd(f.ToArray());
        }

        /**
         * Replace a term in a tree of terms
         */
        public void replaceTerm(ref Term origReplaced, Term orig, Term find, Term replace, Boolean byString)
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
                    Term[] ts;

                    switch (orig.GetKind())
                    {
                        case TermKind.Quantifier:
                            ts = new Term[] { orig.GetQuantifier().Body };
                            break;
                        case TermKind.App:
                            FuncDecl fd = orig.GetAppDecl(); // todo: do the replacement on this---make another function do this replacement only for priming and unpriming (will be much faster)
                            ts = orig.GetAppArgs();
                            break;
                        case TermKind.Numeral: // bottom of tree
                            return;
                        case TermKind.Var:
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
                    origReplaced = this.UpdateTerm(origReplaced, ts);
                    //}
                }
                catch (Microsoft.Z3.Z3Error e)
                {
                }
            }
        }

        public Term replaceIndices(Term t, Term[] oldIndices, Term[] newIndices)
        {
            uint c = uint.MaxValue;

            if (oldIndices.Length == oldIndices.Length)
            {
                Term[] placeholder = new Term[oldIndices.Length];
                for (int i = 0; i < oldIndices.Length; i++)
                {
                    placeholder[i] = this.MkIntNumeral(c);
                    this.replaceTerm(ref t, t, oldIndices[i], placeholder[i], false); // i -> p
                    c--;
                }

                for (int i = 0; i < oldIndices.Length; i++)
                {
                    this.replaceTerm(ref t, t, placeholder[i], newIndices[i], false); // p -> j
                }
            }
            return t;
        }

        /**
         * Check a term
         */
        public Boolean checkTerm(Term t, out Model model, params Boolean[] options)
        {
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
                Console.WriteLine("Term:\n\r" + t.ToString());
            }

            /* save the current state of the context */
            this.Push();

            this.AssertCnstr(t);

            Term proof = null;
            Term[] core;
            //switch (this.CheckAndGetModel(out model))
            //switch (this.CheckAssumptions(out model, new Term[] {this.GetAssignments()}, out proof, out core))
            switch (this.CheckAssumptions(out model, null, out proof, out core))
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
                //model.Dispose(); // todo: add a smarter way to handle this, currently done elsewhere after printing
            }

            if (debug)
            {
                this.DisplayStatistics(Console.Out);
            }

            this.Pop(1);

            return ret;
        }

        /**
         * Prove a term (negation is unsat)
         */
        public Boolean proveTerm(Term t, out Model model, params Boolean[] options)
        {
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
                Console.WriteLine("Term:\n\r" + t.ToString());
            }

            /* save the current state of the context */
            this.Push();

            this.AssertCnstr( !t); // proved if negation is unsat
            
            this.Push();
            Console.WriteLine("\n\r\n\rAttempting to prove the following: \n\r" + this.GetAssignments().ToString() + "\n\r\n\r\n\r");
            this.Pop(1);

            Term proof = null;
            Term[] core;
            //switch (this.CheckAndGetModel(out model))
            switch (this.CheckAssumptions(out model, null, out proof, out core))
            {
                case LBool.False:
                    if (debug)
                    {
                        Console.WriteLine("unsat: proved claim");
                    }
                    ret = true; // proved if negation is unsat
                    break;
                case LBool.Undef:
                    if (debug)
                    {
                        Console.WriteLine("unknown: quantifier elimination failure");
                    }
                    ret = false; // may occur semantics
                    // todo: add breakpoint back and check when this gets hit
                    break;
                case LBool.True:
                    if (debug)
                    {
                        Console.WriteLine("sat: disproved claim");
                        model.Display(Console.Out);
                    }
                    ret = false;
                    break;
            }
            if (model != null)
            {
                //model.Dispose(); // todo: add a smarter way to handle this: current printing model elsewhere
            }

            if (debug)
            {
                this.DisplayStatistics(Console.Out);
            }

            /* restore context */
            this.Pop(1);

            return ret;
        }

        public static String toStringLatex(Term t)
        {
            String s = "";
            TermKind a = t.GetKind();
            

            Term[] args = t.GetAppArgs();

            if (args != null)
            {
                DeclKind k = t.GetAppDecl().GetKind();

                if (args.Length >= 2)
                {
                    uint i = 0;
                    do 
                    {
                        s += toStringLatex(args[i]);
                        switch (k)
                        {

                            case DeclKind.Add:
                                s += " + ";
                                break;
                            case DeclKind.And:
                                s += " \\wedge ";
                                break;
                            case DeclKind.Complement:
                                s += " \\not ";
                                break;
                            case DeclKind.Difference:
                                s += " \\setminus ";
                                break;
                            case DeclKind.Distinct:
                                break;
                            case DeclKind.Div:
                                s += " / ";
                                break;
                            case DeclKind.Eq:
                                s += " = ";
                                break;
                            case DeclKind.False:
                                s += " \\false ";
                                break;
                            case DeclKind.Ge:
                                s += " \\geq ";
                                break;
                            case DeclKind.Gt:
                                s += " > ";
                                break;
                            case DeclKind.Iff:
                                s += " \\Leftrightarrow ";
                                break;
                            case DeclKind.Implies:
                                s += " \\Rightarrow ";
                                break;
                            case DeclKind.Intersect:
                                s += " \\cap ";
                                break;
                            case DeclKind.Ite:
                                break;
                            case DeclKind.Le:
                                s += " \\leq ";
                                break;
                            case DeclKind.Lt:
                                s += " < ";
                                break;
                            case DeclKind.Mod:
                            case DeclKind.Mul:
                                s += " * ";
                                break;
                            case DeclKind.Not:
                                s += " \\neg ";
                                break;
                            case DeclKind.Or:
                                s += " \\vee ";
                                break;
                            case DeclKind.Rem:
                                break;
                            case DeclKind.Sub:
                                s += " - ";
                                break;
                            case DeclKind.Subset:
                                s += " \\subset ";
                                break;
                            case DeclKind.True:
                                s += " \\true ";
                                break;
                            case DeclKind.Uminus:
                                s += " - ";
                                break;
                            case DeclKind.Union:
                                s += " \\cup ";
                                break;
                            case DeclKind.Xor:
                                break;
                            default:
                                break;
                        }
                        i++;
                    } while (i < args.Length - 1);
                    //s += toStringLatex(args[i]);
                }
            }
            return s;
        }

        /**
         * Check an array of terms
         */
        public Boolean checkTerms(Term[] t)
        {
            Boolean debug = false;
            Boolean ret = false;

            if (debug)
            {
                Console.WriteLine("Term:\n\r" + t[0].ToString());
                Console.WriteLine("Term:\n\r" + t[1].ToString());
            }

            /* save the current state of the context */
            this.Push();

            this.AssertCnstr(t[0]);
            this.AssertCnstr(t[1]);
            //this._z3.AssertCnstr(this._z3.MkNot(t));

            //Term not_f = this._z3.MkNot(guard);
            //this._z3.AssertCnstr(not_f);

            Model model = null;
            switch (this.CheckAndGetModel(out model))
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

            /* restore context */
            this.Pop(1);

            return ret;
        }
    }
}
