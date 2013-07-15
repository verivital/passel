using System;
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
using System.Text.RegularExpressions;

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

    public enum PropertyAttributes
    {
        comment,
        equn,
        type,
        post,
        template,   // for synthesis
        format, // our syntax or smtlib
        assumed,
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
        initially,
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
        processes,
    };

    public enum ActionAttributes
    {
        equn
    };

    public enum AutomatonAttributes
    {
        name
    };

    public enum ParameterAttributes
    {
        comment,
        name,
        type,
        assumption,
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
        /// <summary>
        /// Parse a parameter (variable that is constant)
        /// </summary>
        /// <param name="reader"></param>
        /// <returns></returns>
        public static Variable ParseVariableParameter(XmlTextReader reader)
        {
            String name = reader.GetAttribute(ParameterAttributes.name.ToString());
            String type = reader.GetAttribute(ParameterAttributes.type.ToString());
            String comment = reader.GetAttribute(ParameterAttributes.comment.ToString());
            String assumption = reader.GetAttribute(ParameterAttributes.assumption.ToString());

            Variable p = new VariableParameter(name, (Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true), Variable.VarUpdateType.constant, assumption);
            return p;
        }

        /// <summary>
        /// Parse a property (e.g., user supplied safety property, etc.)
        /// </summary>
        /// <param name="reader"></param>
        /// <returns></returns>
        public static Property ParseProperty(XmlTextReader reader)
        {
            if (Controller.Instance.Sys == null)
            {
                throw new System.NullReferenceException("Error parsing property: automaton not specified properly before reaching property.");
            }

            String pstr = reader.GetAttribute(PropertyAttributes.equn.ToString());
            String type = reader.GetAttribute(PropertyAttributes.type.ToString());
            String template = reader.GetAttribute(PropertyAttributes.template.ToString());
            String post = reader.GetAttribute(PropertyAttributes.post.ToString());
            String format = reader.GetAttribute(PropertyAttributes.format.ToString());
            String assumed = reader.GetAttribute(PropertyAttributes.assumed.ToString());

            Property.PropertyType pt;
            Property p;

            // todo: make parsing consistent: either handle it all here, or handle it all in the object (makes more sense)
            if (Enum.TryParse<Property.PropertyType>(type, true, out pt))
            {
                if (format == "smt")
                {
                    p = Property.PropertyFromSmt(pstr);
                    p.makePost(); // update post expression
                    p.Type = Property.PropertyType.safety; // todo: generalize
                }
                else
                {
                    p = new Property(pstr, pt, post, template);
                }
                p.SourceType = SourceTypes.user;
                Controller.Instance.Sys.Properties.Add(p);

                if (assumed == "1")
                {
                    Controller.Instance.Z3.Assumptions.Add((BoolExpr)p.Formula);
                    p.makePost();
                    Controller.Instance.Z3.Assumptions.Add((BoolExpr)p.Post);
                }
            }
            else
            {
                throw new System.Exception("Error parsing property: property type not recognized.");
            }
            return p;
        }

        /// <summary>
        /// Parse a user supplied assumption: also asserts it into Z3
        /// </summary>
        /// <param name="reader"></param>
        public static void ParseAssumption(XmlTextReader reader)
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
        }


        public static void ParseReset(XmlTextReader reader, Transition t)
        {
            if (t == null)
            {
                throw new System.ArgumentNullException("Error parsing transition: transition not specified properly before reaching reset.");
            }

            String reset = reader.GetAttribute(ActionAttributes.equn.ToString());
            if (reset.Length > 0)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(reset);
                t.Reset = LogicalExpression.CreateTerm(tmptree);
            }
        }

        /// <summary>
        /// Parse an ODE
        /// </summary>
        /// <param name="reader"></param>
        /// <param name="h"></param>
        /// <param name="l"></param>
        public static void ParseDAI(XmlTextReader reader, AHybridAutomaton h, ConcreteLocation l)
        {
            if (h == null)
            {
                throw new System.ArgumentNullException("Error parsing transition: hybrid automaton not specified properly before reaching differential equation.");
            }

            if (l == null)
            {
                throw new System.ArgumentNullException("Error parsing transition: location not specified properly before reaching differential equation.");
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
                    if (constants.Count + pvars.Count < 1)
                    {
                        f.DynamicsType = Flow.DynamicsTypes.timed;
                    }
                    else if (constants.Count + pvars.Count == 1)
                    {
                        f.DynamicsType = Flow.DynamicsTypes.timed;
                        if (pvars.Count == 1)
                        {
                            f.RectRateA = Controller.Instance.Params[pvars[0]];
                            f.RectRateB = Controller.Instance.Params[pvars[0]]; // \dot{x} \in [a,a]
                        }
                        if (constants.Count == 1)
                        {
                            f.RectRateA = Controller.Instance.Z3.MkReal(constants[0]);
                            f.RectRateB = Controller.Instance.Z3.MkReal(constants[0]);
                        }
                    }
                    else if (constants.Count + pvars.Count == 2)
                    {
                        f.DynamicsType = Flow.DynamicsTypes.rectangular;
                        // todo: generalize
                        if (pvars.Count >= 1)
                        {
                            f.RectRateA = Controller.Instance.Params[pvars[0]];
                        }
                        if (pvars.Count >= 2)
                        {
                            f.RectRateB = Controller.Instance.Params[pvars[1]];
                        }
                        if (constants.Count >= 1)
                        {
                            f.RectRateA = Controller.Instance.Z3.MkReal(constants[0]);
                        }
                        if (constants.Count >= 2)
                        {
                            f.RectRateB = Controller.Instance.Z3.MkReal(constants[1]);
                        }
                    }

                    if (pvars.Count > 0)
                    {
                        foreach (var y in pvars)
                        {
                            // todo: generalize, this is pretty nasty, and currently only supports dynamics of the form: v[i] R y, where R is an order/equivalence relation (e.g., >, <, >=, <=, =, etc.)
                            Expr addDeltaMin = Controller.Instance.Z3.MkAdd((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], Controller.Instance.Z3.MkMul((ArithExpr)Controller.Instance.Params[y], (ArithExpr)t1));
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
                                Expr addDeltaMin = Controller.Instance.Z3.MkAdd((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], (ArithExpr)t1);
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                            else if (cint == -1) // todo: constants will never be negative currently due to the way findRealConstants function works (- is a unary term, so the constants are always positive with another unary minus outside)
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                Expr addDeltaMin = Controller.Instance.Z3.MkSub((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], (ArithExpr)t1);
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                            else if (cint < 0)
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                Expr addDeltaMin = Controller.Instance.Z3.MkSub((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], Controller.Instance.Z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                            else
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                Expr addDeltaMin = Controller.Instance.Z3.MkAdd((ArithExpr)Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")], Controller.Instance.Z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                        }
                    }
                }
                else // global variables
                {
                    String variableName = variable;
                    f.Variable = Controller.Instance.Sys.GetVariableByName(variableName);

                    // prime the continuous variable occurrences
                    expr = expr.Substitute(Controller.Instance.GlobalVariables[variableName], Controller.Instance.GlobalVariablesPrimed[variableName]);

                    if (pvars.Count > 0)
                    {
                        foreach (var y in pvars)
                        {
                            // todo: generalize, this is pretty nasty, and currently only supports dynamics of the form: v[i] R y, where R is an order/equivalence relation (e.g., >, <, >=, <=, =, etc.)
                            Expr addDeltaMin = Controller.Instance.Z3.MkAdd((ArithExpr)Controller.Instance.Params[variableName], Controller.Instance.Z3.MkMul((ArithExpr)Controller.Instance.Params[y], (ArithExpr)t1));
                            expr = expr.Substitute(Controller.Instance.Params[y], addDeltaMin);
                        }
                    }
                    else if (constants.Count > 0)
                    {
                        foreach (var cs in constants)
                        {
                            int cint = (int)float.Parse(cs);
                            String cstr = float.Parse(cs).ToString();
                            f.DynamicsType = Flow.DynamicsTypes.timed;
                            if (cint == 1)
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                f.RectRateA = c;
                                Expr addDeltaMin = Controller.Instance.Z3.MkAdd((ArithExpr)Controller.Instance.GlobalVariables[variableName], (ArithExpr)t1);
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                            else if (cint == -1)
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                f.RectRateA = c;
                                Expr addDeltaMin = Controller.Instance.Z3.MkSub((ArithExpr)Controller.Instance.GlobalVariables[variableName], (ArithExpr)t1);
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                            else if (cint < 0)
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                f.RectRateA = c;
                                Expr addDeltaMin = Controller.Instance.Z3.MkSub((ArithExpr)Controller.Instance.GlobalVariables[variableName], Controller.Instance.Z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                            else
                            {
                                Expr c = Controller.Instance.Z3.MkReal(cstr);
                                f.RectRateA = c;
                                Expr addDeltaMin = Controller.Instance.Z3.MkAdd((ArithExpr)Controller.Instance.GlobalVariables[variableName], Controller.Instance.Z3.MkMul((ArithExpr)c, (ArithExpr)t1));
                                expr = expr.Substitute(c, addDeltaMin);
                            }
                        }
                    }
                }

                // todo: generalize: we assume anything with a 0 in it is constant dynamics
                //if (!Controller.Instance.Z3.findTerm(expr, Controller.Instance.RealZero, true))
                if (!(f.RectRateA == Controller.Instance.RealZero || f.RectRateB == Controller.Instance.RealZero))
                {
                    f.Value = expr;
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
                else
                {
                    f.DynamicsType = Flow.DynamicsTypes.constant; // no change
                    f.RectRateA = Controller.Instance.RealZero;
                    f.RectRateB = Controller.Instance.RealZero;
                    Expr atmp = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(f.Variable.Name, "i")];
                    Expr btmp = Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<string, string>(f.Variable.Name + Controller.PRIME_SUFFIX, "i")];
                    f.Value = Controller.Instance.Z3.MkEq(atmp, btmp);
                }

                l.Flows.Add(f);
            }
        }

        /// <summary>
        /// Parse the guard of a transition
        /// </summary>
        /// <param name="reader"></param>
        /// <param name="t"></param>
        public static void ParseGuard(XmlTextReader reader, Transition t)
        {
            if (t == null)
            {
                throw new System.ArgumentNullException("Error parsing transition: transition not specified properly before reaching guard.");
            }

            String guard = reader.GetAttribute(GuardAttributes.equn.ToString());
            if (guard.Length > 0)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(guard);
                t.Guard = LogicalExpression.CreateTerm(tmptree);
            }
        }

        /// <summary>
        /// Parse a location (mode)
        /// </summary>
        /// <param name="reader"></param>
        /// <param name="h"></param>
        /// <returns></returns>
        public static ConcreteLocation ParseLocation(XmlTextReader reader, AHybridAutomaton h)
        {
            if (h == null)
            {
                throw new System.ArgumentNullException("Error parsing transition: hybrid automaton not specified properly before reaching location.");
            }
            uint value = UInt32.Parse(reader.GetAttribute(LocationAttributes.id.ToString()));
            String label = reader.GetAttribute(LocationAttributes.name.ToString());
            Boolean initial = Boolean.Parse(reader.GetAttribute(LocationAttributes.initial.ToString()));

            // dynamically create label name if none specified
            if (label.Length == 0)
            {
                label = "loc" + loc_counter;
                loc_counter++;
            }
            if (!Controller.Instance.LocationNumToName.ContainsKey(value))
            {
                Controller.Instance.LocationNumToName.Add(value, label);
            }
            if (!Controller.Instance.LocationNameToNum.ContainsKey(label))
            {
                Controller.Instance.LocationNameToNum.Add(label, value);
            }
            ConcreteLocation l = new ConcreteLocation(h, label, value, initial);
            // bound control location variable values: 0 <= q_i <= # states, 0 <= q_j <= # states, 0 <= q_k <= # states

            return l;
        }

        /// <summary>
        /// Parse location end tag
        /// </summary>
        /// <param name="l"></param>
        public static void ParseLocationEnd(XmlTextReader reader, AHybridAutomaton h, ConcreteLocation l)
        {
            h.addLocation(l);
        }

        /// <summary>
        /// Parse a transition
        /// </summary>
        /// <param name="reader"></param>
        /// <param name="h"></param>
        /// <param name="l"></param>
        /// <returns></returns>
        public static Transition ParseTransition(XmlTextReader reader, AHybridAutomaton h, ConcreteLocation l)
        {
            Transition t;


            // todo: refactor: check and throw if null on either, but also while checking if parent of l is not null (e.g., these transitions may be local or global)
            if (Controller.Instance.Sys != null || h != null)
            {
                t = new Transition(l); // l is null for global transitions, no parent

                if (h == null)
                {
                    Controller.Instance.Sys.addTransition(t);
                }
                else
                {
                    String des = reader.GetAttribute(TransitionAttributes.destination.ToString());
                    String src = reader.GetAttribute(TransitionAttributes.source.ToString());
                    String prs = reader.GetAttribute(TransitionAttributes.processes.ToString());

                    List<String> dess = new List<String>();
                    List<String> srcs = new List<String>();
                    List<String> processes = new List<string>();

                    if (!src.Contains(","))
                    {
                        srcs.Add(src);
                    }
                    else
                    {
                        srcs.AddRange(src.Split(','));
                    }

                    bool toSelf = false;
                    if (des != null && des.Length > 0)
                    {
                        if (!des.Contains(","))
                        {
                            dess.Add(des);
                        }
                        else
                        {
                            dess.AddRange(des.Split(','));
                        }
                    }
                    else
                    {
                        toSelf = true; // only self-loops
                        des = src;
                        dess = srcs;
                    }

                    t.Indices.Add("h"); // do not have to include h by default, as it is always the process moving
                    t.Indices.AddRange(processes); // assume process h always included
                    t.Indices = t.Indices.Distinct().ToList(); // ensure distinct

                    List<AState> from = new List<AState>(); // have to find the frome state as well, because in hyxml syntax, transitions are not associated with locations
                    foreach (AState s in h.Locations)
                    {
                        uint desParsed = 0;
                        uint srcParsed = 0;

                        foreach (String stmp in srcs)
                        {
                            UInt32.TryParse(stmp, out srcParsed);

                            if (s.Label == stmp || (srcParsed != null && Regex.IsMatch(stmp, @"^[0-9]+$") && s.Value == UInt32.Parse(stmp)))
                            {
                                from.Add(s);
                            }
                        }

                        foreach (String dtmp in dess)
                        {
                            UInt32.TryParse(dtmp, out desParsed);

                            if (s.Label == dtmp || (desParsed != null && Regex.IsMatch(dtmp, @"^[0-9]+$") && s.Value == UInt32.Parse(dtmp)))
                            {
                                t.NextStates.Add(s);
                            }
                        }
                    }


                    if (from.Count > 0)
                    {
                        foreach (AState ftmp in from)
                        {
                            t.Parent = (ConcreteLocation)ftmp;
                            if (toSelf) // only self-loops
                            {
                                t.NextStates = new List<AState>();
                                t.NextStates.Add(ftmp);
                            }
                            ftmp.addTransition(t);
                        }
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
            return t;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="reader"></param>
        /// <param name="h"></param>
        public static void ParseVariable(XmlTextReader reader, AHybridAutomaton h)
        {
            if (h == null && Controller.Instance.Sys == null)
            {
                throw new System.Exception("Variable expression for automaton or entire system not well defined (appeared outside of automaton or system declaration).");
            }
            else
            {
                String name = reader.GetAttribute(VariableAttributes.name.ToString());
                String type = reader.GetAttribute(VariableAttributes.type.ToString());
                String update_type = reader.GetAttribute(VariableAttributes.update_type.ToString());
                String initially = reader.GetAttribute(VariableAttributes.initially.ToString());

                if (h != null) // local variable
                {
                    // todo: generalize to the actual general parser? we don't really want to allow such complex declarations of variables, but why not...?
                    if (name.Contains("[") && name.Contains("]")) // indexed variable
                    {
                        String[] split = name.Split('[', ']');
                        String varName = split[0];
                        String indexName = split[1];

                        h.addIndexedVariable(varName, (Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true), (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true), initially);
                        // todo: parse the variables
                    }
                }
                else if (Controller.Instance.Sys != null) // global variable
                {
                    Variable v = new VariableGlobal(name, "", (Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true), (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true), initially);
                }
            }
        }

        static int loc_counter = 0;


        /// <summary>
        /// Parse a HyXML formatted file
        ///
        /// Notes:
        /// 1) Assumes guards and invariants are formatted as infix strings (e.g., 5 + x >= y is a valid guard or invariant, whereas (>= (+ 5 x) y) is not)
        /// 2) Assumes resets are formatted as: varToReset' = expr
        /// 3) Assumes differential inclusions are formatted as: x1_dot >= a and x1_dot <= b; more generally, any relations are okay, we just don't support x1_dot \in [a, b]
        /// 
        /// 1) Eventually modify HyLink to generate HyXML using MathML for guards, invariants, and resets
        /// </summary>
        /// <param name="path"></param>
        public static void ParseInputFile(String path)
        {
            Controller.Instance.Sys = new Holism();
            ConcreteHybridAutomaton h = null;
            Transition t = null;
            ConcreteLocation l = null;
            ElementNames n = ElementNames.parameter;

            if (!File.Exists(path))
            {
                throw new FileNotFoundException("Input file not found: " + path);
            }

            XmlTextReader reader = new XmlTextReader(path);
            while (reader.Read())
            {
                try
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
                                            Variable p = ParseVariableParameter(reader);
                                            break;
                                        }

                                    case ElementNames.predicate:
                                        {
                                            break;
                                        }

                                    // since properties can refer to elements of the automata, we save their strings and parse them after all automata have been fully constructed
                                    case ElementNames.property:
                                        {
                                            ParseProperty(reader);
                                            break;
                                        }
                                    case ElementNames.assumption:
                                        {
                                            ParseAssumption(reader);
                                            break;
                                        }
                                    case ElementNames.action:
                                        {
                                            ParseReset(reader, t);
                                            break;
                                        }
                                    case ElementNames.automaton:
                                        {
                                            String name = reader.GetAttribute(AutomatonAttributes.name.ToString());
                                            h = new ConcreteHybridAutomaton(Controller.Instance.Sys, name);
                                            break;
                                        }
                                    case ElementNames.dai:
                                        {
                                            ParseDAI(reader, h, l);
                                            break;
                                        }
                                    case ElementNames.guard:
                                        {
                                            ParseGuard(reader, t);
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
                                            l = ParseLocation(reader, h);
                                            break;
                                        }
                                    case ElementNames.transition:
                                        {
                                            t = ParseTransition(reader, h, l);
                                            break;
                                        }
                                    case ElementNames.variable:
                                        {
                                            ParseVariable(reader, h);
                                            break;
                                        }
                                    case ElementNames.holism:
                                        {
                                            // todo
                                            break;
                                        }
                                    default:
                                        {
                                            throw new Exception("Bad element specified (uncrecognized).");
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
                                            Controller.Instance.Sys.addHybridAutomaton(h);

                                            foreach (var v in Controller.Instance.Sys.Variables)
                                            {
                                                if (v.UpdateType == Variable.VarUpdateType.discrete && v.Type == Variable.VarType.index)
                                                {
                                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.IntZero, (ArithExpr)Controller.Instance.GlobalVariables[v.Name]));
                                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.GlobalVariables[v.Name], (ArithExpr)Controller.Instance.Params["N"]));
                                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.IntZero, (ArithExpr)Controller.Instance.GlobalVariablesPrimed[v.Name]));
                                                    Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkLe((ArithExpr)Controller.Instance.GlobalVariablesPrimed[v.Name], (ArithExpr)Controller.Instance.Params["N"]));
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
                                            ParseHyXML.ParseLocationEnd(reader, h, l);
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
                catch (NoViableAltException ex)
                {
                    System.Console.WriteLine("ERROR: parser error");
                    System.Console.WriteLine("Line " + reader.LineNumber + " position " + reader.LinePosition + " element name " + reader.Name);
                }
                catch (Exception ex)
                {
                    System.Console.WriteLine("ERROR: parser error");
                    System.Console.WriteLine("Line " + reader.LineNumber + " position " + reader.LinePosition + " element name " + reader.Name);
                }
            }
            reader.Close();
        }
    }
}
