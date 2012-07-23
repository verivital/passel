﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Linq.Expressions;
using System.Text;

using System.Xml;
using System.IO;

using Antlr;
using Antlr.Runtime;
using Antlr.Runtime.Misc;

using Microsoft.Z3;

using passel.controller.smt.z3;

using passel.model;
using passel.controller;
using passel.controller.parsing;
using passel.controller.parsing.math;
using passel.controller.parsing.math.ast;

namespace passel.controller.parsing
{
    public enum ElementNames
    {
        action,
        assumption,
        automaton,

        dai,

        guard,

        holism,

        initial,
        invariant,

        mode,

        parameter,
        predicate,
        property,

        stop,

        transition,

        uguard, // guard universally quantified over process ids (get moved into forall identity so we don't create an unsatisfiable constraint by saying e.g., if next[j] = i, then next'[j] = 0, else next'[j] = next[j], since we elsewhere also say for all j, next'[j] = next[j])

        variable,   
    };

    public enum VariableUpdateTypes
    {
        Continuous,
        Discrete
    };

    public enum VariableTypes
    {
        Continuous, // todo: remove, temp bug fix
        Discrete,
        Integer,
        Real,
    };

    public enum PropertyAttributes
    {
        comment,
        equn,
        type,
        post,
        template,   // for synthesis
    };

    public enum AssumptionTypes
    {
        invariant,
        safety,
        safety_weak,
        inductive_invariant,
        none
    };

    public enum VariableAttributes
    {
        name,
        scope,
        type,
        update_type,
    };

    public enum LocationAttributes
    {
        id,
        initial,
        name,
    };

    public enum TransitionAttributes
    {
        destination,
        source,
    };

    public enum ActionAttributes
    {
        equn
    };

    public enum ParameterAttributes
    {
        comment,
        name,
        type,
    };

    public enum ParameterTypes
    {
        integer,
        index,
        real,
    };

    public enum AssumptionAttributes
    {
        comment,
        equn,
        type,
    };

    public enum FlowAttributes
    {
        variable,
        equn,
    };

    public enum GuardAttributes
    {
        equn,
    };

    public enum StopAttributes
    {
        equn,
    };

    public enum InitialAttributes
    {
        equn,
    };

    public enum InvariantAttributes
    {
        equn,
    };

    public enum UGuardAttributes
    {
        equn,
    };

    static public class ParseHyXML
    {
        private static Z3Wrapper z3 = Controller.Instance.Z3;

        /*
        public static Antlr.Runtime.Tree.CommonTree allIntsToReals(Antlr.Runtime.Tree.CommonTree t)
        {
            if (t != null)
            {
                switch (t.Type)
                {
                    case guardLexer.INTEGER:
                        {
                            t.Type = guardLexer.FLOAT; // can't modify, doesnt work
                            break;
                        }
                    default:
                        {
                            if (t.ChildCount > 0)
                            {
                                for (int i = 0; i < t.ChildCount; i++)
                                {
                                    t.Children[i] = allIntsToReals((Antlr.Runtime.Tree.CommonTree)t.Children[i]);
                                }
                            }
                            break;
                        }
                }
            }
            return t;
        }
         */

        public static List<Expr> ParseReach(String path)
        {
            List<Expr> reach = new List<Expr>();

            StreamReader reader = new StreamReader(path);
            
            String reachset = reader.ReadToEnd();

            reachset = reachset.Substring(reachset.IndexOf("{"));

            String reachstate = "";
            do
            {
                int start = reachset.IndexOf("&");
                int end = reachset.IndexOf(",");
                if (end < 0)
                {
                    end = reachset.IndexOf("}");
                    if (end < 0)
                    {
                        break;
                    }
                }
                reachstate = reachset.Substring(start + 2, end - (start + 2));
                reachstate = reachstate.Replace("\n", "");
                reachstate = reachstate.Replace("\r", "");
                reachstate = reachstate.Replace("&", "&&");
                reachstate = reachstate.Replace("|", "||");
                reachstate = reachstate.Trim();
                reachstate = reachstate.Substring(1, reachstate.Length - 2); // remove parentheses

                String[] reachsplit = reachstate.Split(' ');

                for (int i = 0; i < reachsplit.Length; i++)
                {
                    String s = reachsplit[i];
                    double o; // unused
                    if (double.TryParse(s, out o))
                    {
                        if (!s.Contains("."))
                        {
                            reachsplit[i] = s + ".0"; // make double
                        }
                    }
                    else if (s.Contains("*"))
                    {
                        String[] factors = s.Split('*');
                        reachsplit[i] = "";

                        for (int j = 0; j < factors.Length; j++)
                        {
                            String f = factors[j];
                            if (double.TryParse(f, out o))
                            {
                                if (!s.Contains("."))
                                {
                                    f += ".0";
                                }
                            }
                            reachsplit[i] += f;
                            if (j < factors.Length - 1)
                            {
                                reachsplit[i] += "*";
                            }
                        }
                    }

                    //if
                }

                // recreate string
                String reachstatereal = "";
                foreach (String s in reachsplit)
                {
                    reachstatereal += s + " ";
                }
                reachstate = reachstatereal;

                for (uint i = 0; i <= Controller.Instance.IndexNValue; i++)
                {
                    // TODO: add function to convert index integer to index symbol (e.g., wrap-around after hitting z, or some other value, and start making indices like ii, ij, ik, ..., iii, iij, etc.)
                    uint idx = 'i' + i;
                    reachstate = reachstate.Replace("_" + (i + 1), "[" + (char)idx + "]"); // add integer to char to get next index (temporary)
                    //reachstate = reachstate.Replace("_2", "[j]");
                    //reachstate = reachstate.Replace("_3", "[k]");
                }

                String loc = reachset.Substring(0, start - 1);
                // assume 1st state is for global automaton

                Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(reachstate);

                Expr rs = LogicalExpression.CreateTerm(tmptree);

                reach.Add(rs);

                reachset = reachset.Substring(end+1); // cut off from reachset
            } while (reachset.Length > 0 || reachset.Contains(","));
            

            return reach;
        }

        /**
         * Parse a HyXML formatted file
         * 
         * Notes:
         * 1) Assumes guards and invariants are formatted as infix strings (e.g., 5 + x >= y is a valid guard or invariant, whereas (>= (+ 5 x) y) is not)
         * 2) Assumes resets are formatted as: varToReset' = expr
         * 3) Assumes differential inclusions are formatted as: x1_dot >= a and x1_dot <= b; more generally, any relations are okay, we just don't support x1_dot \in [a, b]
         * 
         * Todo:
         * 1) Eventually modify HyLink to generate HyXML using MathML for guards, invariants, and resets
         */
        public static Holism ParseFile(String path)
        {
            Holism sys = new Holism();
            ConcreteHybridAutomaton h = null;
            Transition t = null;
            ConcreteLocation l = null;
            ElementNames n = ElementNames.parameter;

            XmlTextReader reader = new XmlTextReader(path);
            while (reader.Read())
            {
                switch (reader.NodeType)
                {
                    case XmlNodeType.Element:
                        {
                            n = (ElementNames)(Enum.Parse(typeof(ElementNames), reader.Name, true));
                            switch (n)
                            {
                                case ElementNames.parameter:
                                    {
                                        String name = reader.GetAttribute(ParameterAttributes.name.ToString());
                                        String type = reader.GetAttribute(ParameterAttributes.type.ToString());
                                        String comment = reader.GetAttribute(ParameterAttributes.comment.ToString());

                                        Expr param = null;
                                        Expr paramPrime = null;

                                        switch ((ParameterTypes)Enum.Parse(typeof(ParameterTypes), type, true))
                                        {
                                            case ParameterTypes.index:
                                                param = Controller.Instance.Z3.MkIntConst(name); // todo: vs Controller.Instance.IndexType
                                                break;

                                            case ParameterTypes.integer:
                                                param = Controller.Instance.Z3.MkIntConst(name);
                                                break;
                                            case ParameterTypes.real:
                                                param = Controller.Instance.Z3.MkRealConst(name);
                                                break;
                                        }

                                        if (param != null)
                                        {
                                            if (!Controller.Instance.Params.ContainsKey(name))
                                            {
                                                Controller.Instance.Params.Add(name, param);
                                            }
                                        }
                                        else
                                        {
                                            throw new System.Exception("Parameter term not created.");
                                        }
                                        break;
                                    }

                                case ElementNames.predicate:
                                    break;

                                // since properties can refer to elements of the automata, we save their strings and parse them after all automata have been fully constructed
                                case ElementNames.property:
                                    {
                                        if (sys == null)
                                        {
                                            throw new System.Exception("Error parsing property: automaton not specified properly before reaching property.");
                                        }

                                        String pstr = reader.GetAttribute(PropertyAttributes.equn.ToString());
                                        String type = reader.GetAttribute(PropertyAttributes.type.ToString());
                                        String template = reader.GetAttribute(PropertyAttributes.template.ToString());
                                        String post = reader.GetAttribute(PropertyAttributes.post.ToString());

                                        Property.PropertyType pt;

                                        // todo: make parsing consistent: either handle it all here, or handle it all in the object (makes more sense)
                                        if (Enum.TryParse<Property.PropertyType>(type, true, out pt))
                                        {
                                            Property p = new Property(pstr, pt, post, template);
                                            sys.Properties.Add(p);
                                        }
                                        else
                                        {
                                            throw new System.Exception("Error parsing property: property type not recognized.");
                                        }
                                        break;
                                    }
                                case ElementNames.assumption:
                                    {
                                        String assump = reader.GetAttribute(AssumptionAttributes.equn.ToString());
                                        String type = reader.GetAttribute(AssumptionAttributes.type.ToString());

                                        AssumptionTypes atype;

                                        if (type != null)
                                        {
                                            atype = (AssumptionTypes)Enum.Parse(typeof(AssumptionTypes), type, true);
                                        }
                                        else
                                        {
                                            atype = AssumptionTypes.none;
                                        }

                                        if (assump.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(assump);
                                            Expr assumpTerm = LogicalExpression.CreateTerm(tmptree);

                                            switch (atype)
                                            {
                                                case AssumptionTypes.safety:
                                                case AssumptionTypes.inductive_invariant:
                                                    {
                                                        // assert the assumption
                                                        Expr assumpTermPrime = assumpTerm;
                                                        Controller.Instance.Z3.primeAllVariables(ref assumpTermPrime);

                                                        Expr assumpTermImplies = Controller.Instance.Z3.MkImplies((BoolExpr)assumpTerm, (BoolExpr)assumpTermPrime); // inductive part

                                                        Controller.Instance.Z3.Assumptions.Add((BoolExpr)assumpTerm); // invariant part
                                                        Controller.Instance.Z3.Assumptions.Add((BoolExpr)assumpTermPrime);
                                                        //Controller.Instance.Z3.AssertCnstr(assumpTerm & assumpTermPrime);

                                                        //Controller.Instance.Z3.AssertCnstr(assumpTermImplies);

                                                        break;
                                                    }
                                                case AssumptionTypes.invariant:
                                                case AssumptionTypes.none:
                                                default:
                                                    {
                                                        // assert the assumption
                                                        Controller.Instance.Z3.Assumptions.Add((BoolExpr)assumpTerm);
                                                        break;
                                                    }
                                            }
                                        }

                                        break;
                                    }
                                case ElementNames.action:
                                    {
                                        if (t == null)
                                        {
                                            throw new System.Exception("Error parsing transition: transition not specified properly before reaching action.");
                                        }

                                        String reset = reader.GetAttribute(ActionAttributes.equn.ToString());
                                        if (reset.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(reset);
                                            t.Reset = LogicalExpression.CreateTerm(tmptree);
                                        }
                                        break;
                                    }
                                case ElementNames.automaton:
                                    {
                                        // todo: get name
                                        h = new ConcreteHybridAutomaton(sys);
                                        break;
                                    }
                                case ElementNames.dai:
                                    {
                                        if (l == null)
                                        {
                                            throw new System.Exception("Error parsing transition: location not specified properly before reaching differntial equation.");
                                        }

                                        // todo: this currently has a lot of assumptions about how the diffeq should appear
                                        // todo: probably the easiest way to accomodate this would be to require a different <dai> block in the xml file for each variable
                                        //       but obviously this could have limitations for linear / affine dynamics, but... maybe not?
                                        //       let's think about it more

                                        String variable = reader.GetAttribute(FlowAttributes.variable.ToString());
                                        String flow = reader.GetAttribute(FlowAttributes.equn.ToString());

                                        if (variable != null && flow != null && variable.Length > 0 && flow.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(flow);
                                            List<String> vars = LogicalExpression.findContinuousVars(tmptree);
                                            List<String> pvars = LogicalExpression.findParams(tmptree);
                                            List<String> constants = LogicalExpression.findAllRealConstants(tmptree);
                                            Expr expr = LogicalExpression.CreateTerm(tmptree);
                                            List<Expr> flows = new List<Expr>();
                                            Expr t1 = Controller.Instance.Z3.MkRealConst("t_1");

                                            Flow f = new Flow();

                                            // indexed if the variable appears e.g., as x[i], else assume global, e.g., x
                                            if (variable.Contains("[") && variable.Contains("]"))
                                            {
                                                String[] vns = variable.Split('[');
                                                String variableName = vns[0]; // todo: error handling

                                                f.Variable = h.GetVariableByName(variableName); // todo: error handling

                                                // prime all variables
                                                switch (Controller.Instance.DataOption)
                                                {
                                                    case Controller.DataOptionType.array:
                                                        {
                                                            expr = expr.Substitute(Controller.Instance.DataA.IndexedVariableDecl[variableName], Controller.Instance.DataA.IndexedVariableDeclPrimed[variableName]);
                                                            break;
                                                        }
                                                    case Controller.DataOptionType.uninterpreted_function:
                                                    default:
                                                        {
                                                            Controller.Instance.Z3.replaceFuncDecl(ref expr, expr, Controller.Instance.DataU.IndexedVariableDecl[variableName], Controller.Instance.DataU.IndexedVariableDeclPrimed[variableName], false);
                                                            break;
                                                        }
                                                }

                                                // todo: rewrite in more general form for timed vs. rectangular
                                                if (constants.Count + pvars.Count <= 1)
                                                {
                                                    f.DynamicsType = Flow.DynamicsTypes.timed;
                                                }
                                                else if (constants.Count + pvars.Count == 2)
                                                {
                                                    f.DynamicsType = Flow.DynamicsTypes.rectangular;

                                                    // todo: generalize
                                                    f.RectRateA = Controller.Instance.Params[pvars[0]];
                                                    f.RectRateB = Controller.Instance.Params[pvars[1]];
                                                }

                                                if (pvars.Count > 0)
                                                {
                                                    foreach (var y in pvars)
                                                    {
                                                        // todo: generalize, this is pretty nasty, and currently only supports dynamics of the form: v[i] R y, where R is an order/equivalence relation (e.g., >, <, >=, <=, =, etc.)
                                                        Expr addDeltaMin = z3.MkAdd((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], z3.MkMul((ArithExpr)Controller.Instance.Params[y], (ArithExpr)t1));
                                                        expr = expr.Substitute(Controller.Instance.Params[y], addDeltaMin);
                                                    }
                                                }
                                                else if (constants.Count > 0)
                                                {
                                                    foreach (var cs in constants)
                                                    {
                                                        int cint = (int)float.Parse(cs);
                                                        String cstr = float.Parse(cs).ToString();

                                                        if (cint == 1)
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkAdd((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], (ArithExpr)t1);
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                        else if (cint == -1) // todo: constants will never be negative currently due to the way findRealConstants function works (- is a unary term, so the constants are always positive with another unary minus outside)
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkSub((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], (ArithExpr)t1);
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                        else if (cint < 0)
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkSub((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                        else
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkAdd((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                    }
                                                }
                                            }
                                            else // global variables
                                            {
                                                String variableName = variable;
                                                f.Variable = sys.GetVariableByName(variableName);

                                                // prime the continuous variable occurrences
                                                expr = expr.Substitute(Controller.Instance.GlobalVariables[variableName], Controller.Instance.GlobalVariablesPrimed[variableName]);

                                                if (pvars.Count > 0)
                                                {
                                                    foreach (var y in pvars)
                                                    {
                                                        // todo: generalize, this is pretty nasty, and currently only supports dynamics of the form: v[i] R y, where R is an order/equivalence relation (e.g., >, <, >=, <=, =, etc.)
                                                        Expr addDeltaMin = z3.MkAdd((ArithExpr)Controller.Instance.Params[variableName], z3.MkMul((ArithExpr)Controller.Instance.Params[y], (ArithExpr)t1));
                                                        expr = expr.Substitute(Controller.Instance.Params[y], addDeltaMin);
                                                    }
                                                }
                                                else if (constants.Count > 0)
                                                {
                                                    foreach (var cs in constants)
                                                    {
                                                        int cint = (int)float.Parse(cs);
                                                        String cstr = float.Parse(cs).ToString();

                                                        if (cint == 1)
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkAdd((ArithExpr)Controller.Instance.GlobalVariables[variableName], (ArithExpr)t1);
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                        else if (cint == -1)
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkSub((ArithExpr)Controller.Instance.GlobalVariables[variableName], (ArithExpr)t1);
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                        else if (cint < 0)
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkSub((ArithExpr)Controller.Instance.GlobalVariables[variableName], z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                        else
                                                        {
                                                            Expr c = Controller.Instance.Z3.MkReal(cstr);
                                                            Expr addDeltaMin = z3.MkAdd((ArithExpr)Controller.Instance.GlobalVariables[variableName], z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                                            expr = expr.Substitute(c, addDeltaMin);
                                                        }
                                                    }
                                                }
                                            }

                                            // todo: generalize: we assume anything with a 0 in it is constant dynamics
                                            if (!Controller.Instance.Z3.findTerm(expr, Controller.Instance.RealZero, true))
                                            {
                                                f.Value = expr;
                                                l.Flows.Add(f);
                                                /*
                                                // todo: move zero diffeq detection to this part, as currently we may be removing some actual diffeqs if any of them are 0
                                                if (l.Flow != null)
                                                {
                                                    l.Flow = l.Flow & expr;
                                                }
                                                else
                                                {
                                                    l.Flow = expr; // todo: this doesn't work properly if we have multiple variables, due to the way we replace the flow in stopping conditions and invariants
                                                    // one solution is to use a list of flows
                                                    // another is to create a flow object, which is the more natural choice, and keep a list of flow objects (so they may have different types, e.g., timed vs rect vs linear)
                                                }
                                                 */
                                            }
                                        }

                                        break;
                                    }
                                case ElementNames.guard:
                                    {
                                        if (t == null)
                                        {
                                            throw new System.Exception("Error parsing transition: transition not specified properly before reaching guard.");
                                        }

                                        String guard = reader.GetAttribute(GuardAttributes.equn.ToString());
                                        if (guard.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(guard);
                                            t.Guard = LogicalExpression.CreateTerm(tmptree);
                                        }

                                        break;
                                    }
                                case ElementNames.uguard:
                                    {
                                        if (t == null)
                                        {
                                            throw new System.Exception("Error parsing transition: transition not specified properly before reaching universally quantified guard.");
                                        }

                                        String uguard = reader.GetAttribute(GuardAttributes.equn.ToString());
                                        if (uguard.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(uguard);
                                            t.UGuard = LogicalExpression.CreateTerm(tmptree);
                                        }

                                        break;
                                    }
                                case ElementNames.initial:
                                    {
                                        if (h == null)
                                        {
                                            throw new System.Exception("Error parsing initial: automaton not specified properly before reaching initial.");
                                        }

                                        String init = reader.GetAttribute(InitialAttributes.equn.ToString());
                                        if (init.Length > 0)
                                        {
                                            h.InitialString = init;
                                        }

                                        break;
                                    }
                                case ElementNames.invariant:
                                    {
                                        if (l == null)
                                        {
                                            throw new System.Exception("Error parsing transition: location not specified properly before reaching invariant.");
                                        }

                                        String inv = reader.GetAttribute(InvariantAttributes.equn.ToString());
                                        if (inv.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(inv);
                                            l.Invariant = LogicalExpression.CreateTerm(tmptree);
                                        }

                                        break;
                                    }
                                case ElementNames.stop:
                                    {
                                        if (l == null)
                                        {
                                            throw new System.Exception("Error parsing transition: location not specified properly before reaching stopping condition.");
                                        }

                                        String stop = reader.GetAttribute(StopAttributes.equn.ToString());
                                        if (stop.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(stop);
                                            l.Stop = LogicalExpression.CreateTerm(tmptree);
                                        }

                                        break;
                                    }
                                case ElementNames.mode:
                                    {
                                        if (h == null)
                                        {
                                            throw new System.Exception("Error parsing transition: hybrid automaton not specified properly before reaching location.");
                                        }
                                        UInt32 value = UInt32.Parse(reader.GetAttribute(LocationAttributes.id.ToString()));
                                        String label = reader.GetAttribute(LocationAttributes.name.ToString());
                                        Boolean initial = Boolean.Parse(reader.GetAttribute(LocationAttributes.initial.ToString()));
                                        Controller.Instance.LocationNumToName.Add(value, label);
                                        l = new ConcreteLocation(label, value, initial);
                                        // bound control location variable values: 0 <= q_i <= # states, 0 <= q_j <= # states, 0 <= q_k <= # states
                                        break;
                                    }
                                case ElementNames.transition:
                                    {
                                        if (sys != null || h != null)
                                        {
                                            t = new Transition();

                                            if (h == null)
                                            {
                                                sys.addTransition(t);
                                            }
                                            else
                                            {

                                                AState from = null; // have to find the frome state as well, because in hyxml syntax, transitions are not associated with locations
                                                foreach (AState s in h.Locations)
                                                {
                                                    String des = reader.GetAttribute(TransitionAttributes.destination.ToString());
                                                    String src = reader.GetAttribute(TransitionAttributes.source.ToString());
                                                    // todo: build hash table after found once

                                                    UInt32 desParsed;
                                                    UInt32.TryParse(des, out desParsed);
                                                    UInt32 srcParsed;
                                                    UInt32.TryParse(src, out srcParsed);

                                                    if (s.Label == des || (desParsed != 0 && s.Value == UInt32.Parse(des)))
                                                    {
                                                        t.NextStates.Add(s);
                                                    }

                                                    if (s.Label == src || (srcParsed != 0 && s.Value == UInt32.Parse(src)))
                                                    {
                                                        from = s;
                                                    }
                                                }

                                                if (from != null)
                                                {
                                                    from.addTransition(t);
                                                }
                                                else
                                                {
                                                    throw new System.Exception("Error parsing transition: could not find the source location.");
                                                }
                                            }
                                        }
                                        else
                                        {
                                            throw new System.Exception("Error parsing transition: either holism or hybrid automaton not specified properly before reaching transition.");
                                        }


                                        break;
                                    }
                                case ElementNames.variable:
                                    {
                                        if (h == null && sys == null)
                                        {
                                            throw new System.Exception("Variable expression for automaton or entire system not well defined (appeared outside of automaton or system declaration).");
                                        }
                                        else
                                        {
                                            String name = reader.GetAttribute(VariableAttributes.name.ToString());
                                            String type = reader.GetAttribute(VariableAttributes.type.ToString());
                                            String update_type = reader.GetAttribute(VariableAttributes.update_type.ToString());

                                            if (h != null) // local variable
                                            {
                                                // todo: generalize to the actual general parser? we don't really want to allow such complex declarations of variables, but why not...?
                                                if (name.Contains("[") && name.Contains("]")) // indexed variable
                                                {
                                                    String[] split = name.Split('[', ']');
                                                    String varName = split[0];
                                                    String indexName = split[1];

                                                    h.addIndexedVariable(varName, (Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true), (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true));
                                                    // todo: parse the variables
                                                }
                                            }
                                            else if (sys != null) // global variable
                                            {
                                                Expr globalVariable = null;
                                                Expr globalVariablePrime = null;

                                                Variable v = new Variable();
                                                v.Name = name;
                                                v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);

                                                //switch ((ParameterTypes)Enum.Parse(typeof(ParameterTypes), type, true))
                                                // todo: next blockcan likely be converted (for the most part) into a function call instead of switch (e.g., lots of repition)
                                                switch ((Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true))
                                                {
                                                    case Variable.VarType.boolean:
                                                        globalVariable = Controller.Instance.Z3.MkBoolConst(name);
                                                        v.Type = Variable.VarType.boolean;
                                                        globalVariablePrime = Controller.Instance.Z3.MkBoolConst(name + Controller.PRIME_SUFFIX);
                                                        break;
                                                    case Variable.VarType.index:
                                                        globalVariable = Controller.Instance.Z3.MkIntConst(name); // todo: vs Controller.Instance.IndexType
                                                        v.Type = Variable.VarType.index;
                                                        globalVariablePrime = Controller.Instance.Z3.MkIntConst(name + Controller.PRIME_SUFFIX); // todo: vs Controller.Instance.IndexType
                                                        break;
                                                    case Variable.VarType.integer:
                                                        globalVariable = Controller.Instance.Z3.MkIntConst(name);
                                                        v.Type = Variable.VarType.integer;
                                                        v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                        globalVariablePrime = Controller.Instance.Z3.MkIntConst(name + Controller.PRIME_SUFFIX);
                                                        break;
                                                    case Variable.VarType.real:
                                                        globalVariable = Controller.Instance.Z3.MkRealConst(name);
                                                        v.Type = Variable.VarType.real;
                                                        v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                        globalVariablePrime = Controller.Instance.Z3.MkRealConst(name + Controller.PRIME_SUFFIX);
                                                        break;
                                                    case Variable.VarType.nnreal:
                                                        globalVariable = Controller.Instance.Z3.MkRealConst(name);
                                                        v.Type = Variable.VarType.nnreal;
                                                        v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                        globalVariablePrime = Controller.Instance.Z3.MkRealConst(name + Controller.PRIME_SUFFIX);
                                                        break;
                                                }

                                                if (globalVariable != null && globalVariablePrime != null)
                                                {
                                                    if (!Controller.Instance.GlobalVariables.ContainsKey(name))
                                                    {
                                                        sys.Variables.Add(v);
                                                        Controller.Instance.GlobalVariables.Add(name, globalVariable);
                                                        Controller.Instance.GlobalVariablesPrimed.Add(name, globalVariablePrime);
                                                    }
                                                }
                                                else
                                                {
                                                    throw new System.Exception("Parameter term not created.");
                                                }
                                            }
                                        }
                                        
                                        break;
                                    }
                                default:
                                    {
                                        break;
                                    }
                            }

                            break;
                        }
                    // destroy temporary arguments
                    case XmlNodeType.EndElement:
                        {
                            n = (ElementNames)(Enum.Parse(typeof(ElementNames), reader.Name, true));
                            switch (n)
                            {
                                case ElementNames.parameter:
                                    {
                                        break;
                                    }
                                case ElementNames.action:
                                    {
                                        break;
                                    }
                                case ElementNames.automaton:
                                    {
                                        h.finishConstruction(); // finish building the concrete automaton: create equations for initial conditions, assert constraints on locations, etc.
                                        sys.addHybridAutomaton(h);

                                        foreach (var v in sys.Variables)
                                        {
                                            if (v.UpdateType == Variable.VarUpdateType.discrete && v.Type == Variable.VarType.index)
                                            {
                                                z3.Assumptions.Add(z3.MkAnd(z3.MkLe((ArithExpr)Controller.Instance.IntZero, (ArithExpr)Controller.Instance.GlobalVariables[v.Name]), z3.MkLe((ArithExpr)Controller.Instance.GlobalVariables[v.Name], (ArithExpr)Controller.Instance.Params["N"])));
                                                z3.Assumptions.Add(z3.MkAnd(z3.MkLe((ArithExpr)Controller.Instance.IntZero, (ArithExpr)Controller.Instance.GlobalVariablesPrimed[v.Name]), z3.MkLe((ArithExpr)Controller.Instance.GlobalVariablesPrimed[v.Name], (ArithExpr)Controller.Instance.Params["N"])));
                                            }
                                        }

                                        h = null;
                                        break;
                                    }
                                case ElementNames.dai:
                                    {
                                        break;
                                    }
                                case ElementNames.guard:
                                    {
                                        break;
                                    }
                                case ElementNames.invariant:
                                    {
                                        break;
                                    }
                                case ElementNames.mode:
                                    {
                                        h.addLocation(l);
                                        l = null;
                                        break;
                                    }
                                case ElementNames.transition:
                                    {
                                        //l.addTransition(t);
                                        // todo: search the locations by id to find the prestate and poststate locations
                                        t = null;
                                        break;
                                    }
                                case ElementNames.variable:
                                    {
                                        break;
                                    }
                                default:
                                    {
                                        break;
                                    }
                            }

                            break;
                        }
                    default:
                        {
                            break;
                        }
                }
            }
            reader.Close();

            return sys;
        }
    }
}
