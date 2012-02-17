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

using phyea.model;
using phyea.controller;
using phyea.controller.parsing;
using phyea.controller.parsing.math;
using phyea.controller.parsing.math.ast;

namespace phyea.controller.parsing
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

                                        Term param = null;
                                        Term paramPrime = null;

                                        switch ((ParameterTypes)Enum.Parse(typeof(ParameterTypes), type, true))
                                        {
                                            case ParameterTypes.index:
                                                param = Controller.Instance.Z3.MkConst(name, Controller.Instance.IndexType);
                                                break;

                                            case ParameterTypes.integer:
                                                param = Controller.Instance.Z3.MkConst(name, Controller.Instance.IntType);
                                                break;
                                            case ParameterTypes.real:
                                                param = Controller.Instance.Z3.MkConst(name, Controller.Instance.RealType);
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

                                        String post = reader.GetAttribute("post");

                                        if ((pstr == "forall i ((q[i] == cs or q[i] == trying) implies (g == i and (forall idxj (q[idxj] != waiting))))")  || (pstr == "forall i ((q[i] == cs or q[i] == trying) implies (g == i and (forall j (q[j] != waiting))))")) // todo: remove, bug checking
                                        {
                                            Boolean br = true;
                                        }

                                        Property p = new Property(pstr, (Property.PropertyType)Enum.Parse(typeof(Property.PropertyType), type, true), post);

                                        sys.Properties.Add(p);


                                        //Property pneg = new Property("! ( " + pstr + ")", (Property.PropertyType)Enum.Parse(typeof(Property.PropertyType), type, true));
                                        //sys.Properties.Add(pneg);


                                        //Property pneginside = p;
                                        //p.Formula
                                        //String pstr_repl = pstr;
                                        //System.Text.RegularExpressions.Regex.Replace(pstr_repl, "forall [a-z]+\b",  
                                        //Property pneginside = new Property(, (Property.PropertyType)Enum.Parse(typeof(Property.PropertyType), type, true));
                                        //sys.Properties.Add(pneginside);

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
                                            Term assumpTerm = LogicalExpression.CreateTerm(tmptree);

                                            switch (atype)
                                            {
                                                case AssumptionTypes.safety:
                                                case AssumptionTypes.inductive_invariant:
                                                    {
                                                        // assert the assumption
                                                        Term assumpTermPrime = assumpTerm;
                                                        Controller.Instance.Z3.primeAllVariables(ref assumpTermPrime);

                                                        Term assumpTermImplies = Controller.Instance.Z3.MkImplies(assumpTerm, assumpTermPrime); // inductive part

                                                        Controller.Instance.Z3.AssertCnstr(assumpTerm); // invariant part
                                                        Controller.Instance.Z3.AssertCnstr(assumpTermPrime);
                                                        //Controller.Instance.Z3.AssertCnstr(assumpTerm & assumpTermPrime);

                                                        //Controller.Instance.Z3.AssertCnstr(assumpTermImplies);

                                                        break;
                                                    }
                                                case AssumptionTypes.invariant:
                                                case AssumptionTypes.none:
                                                default:
                                                    {
                                                        // assert the assumption
                                                        Controller.Instance.Z3.AssertCnstr(assumpTerm);
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
                                            Term expr = LogicalExpression.CreateTerm(tmptree);
                                            List<Term> flows = new List<Term>();
                                            Term t1 = Controller.Instance.Z3.MkConst("t_1", Controller.Instance.RealType);

                                            // indexed if the variable appears e.g., as x[i], else assume global, e.g., x
                                            if (variable.Contains("[") && variable.Contains("]"))
                                            {
                                                String[] vns = variable.Split('[');
                                                String variableName = vns[0]; // todo: error handling

                                                // prime all variables
                                                switch (Controller.Instance.DataOption)
                                                {
                                                    case Controller.DataOptionType.array:
                                                        {
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, Controller.Instance.DataA.IndexedVariableDecl[variableName], Controller.Instance.DataA.IndexedVariableDeclPrimed[variableName], false);
                                                            break;
                                                        }
                                                    case Controller.DataOptionType.uninterpreted_function:
                                                    default:
                                                        {
                                                            Controller.Instance.Z3.replaceFuncDecl(ref expr, expr, Controller.Instance.DataU.IndexedVariableDecl[variableName], Controller.Instance.DataU.IndexedVariableDeclPrimed[variableName], false);
                                                            break;
                                                        }
                                                }

                                                // todo: check if this works in general to distinguish timed vs. rectangular
                                                if (constants.Count + pvars.Count <= 1)
                                                {
                                                    l.DynamicsType = Location.DynamicsTypes.timed;
                                                }
                                                else if (constants.Count + pvars.Count == 2)
                                                {
                                                    l.DynamicsType = Location.DynamicsTypes.rectangular;
                                                }

                                                if (pvars.Count > 0)
                                                {
                                                    foreach (var y in pvars)
                                                    {
                                                        // todo: generalize, this is pretty nasty, and currently only supports dynamics of the form: v[i] R y, where R is an order/equivalence relation (e.g., >, <, >=, <=, =, etc.)
                                                        Term addDeltaMin = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")] + (Controller.Instance.Params[y] * t1);
                                                        Controller.Instance.Z3.replaceTerm(ref expr, expr, Controller.Instance.Params[y], addDeltaMin, false);
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
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")] + t1;
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                        else if (cint == -1) // todo: constants will never be negative currently due to the way findRealConstants function works (- is a unary term, so the constants are always positive with another unary minus outside)
                                                        {
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")] - t1;
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                        else if (cint < 0)
                                                        {
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")] - (c * t1);
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                        else
                                                        {
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")] + (c * t1);
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                    }
                                                }
                                            }
                                            else // global variables
                                            {
                                                String variableName = variable;

                                                // prime the continuous variable occurrences
                                                Controller.Instance.Z3.replaceTerm(ref expr, expr, Controller.Instance.GlobalVariables[variableName], Controller.Instance.GlobalVariablesPrimed[variableName], false);

                                                if (pvars.Count > 0)
                                                {
                                                    foreach (var y in pvars)
                                                    {
                                                        // todo: generalize, this is pretty nasty, and currently only supports dynamics of the form: v[i] R y, where R is an order/equivalence relation (e.g., >, <, >=, <=, =, etc.)
                                                        Term addDeltaMin = Controller.Instance.Params[variableName] + (Controller.Instance.Params[y] * t1);
                                                        Controller.Instance.Z3.replaceTerm(ref expr, expr, Controller.Instance.Params[y], addDeltaMin, false);
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
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.GlobalVariables[variableName] + t1;
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                        else if (cint == -1)
                                                        {
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.GlobalVariables[variableName] - t1;
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                        else if (cint < 0)
                                                        {
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.GlobalVariables[variableName] - (c * t1);
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                        else
                                                        {
                                                            Term c = Controller.Instance.Z3.MkRealNumeral(cstr);
                                                            Term addDeltaMin = Controller.Instance.GlobalVariables[variableName] + (c * t1);
                                                            Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
                                                        }
                                                    }
                                                }
                                            }

                                            // todo: generalize: we assume anything with a 0 in it is constant dynamics
                                            if (!Controller.Instance.Z3.findTerm(expr, Controller.Instance.RealZero, true))
                                            {
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
                                                Term globalVariable = null;
                                                Term globalVariablePrime = null;

                                                Variable v = new Variable();
                                                v.Name = name;
                                                v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);

                                                //switch ((ParameterTypes)Enum.Parse(typeof(ParameterTypes), type, true))
                                                // todo: next blockcan likely be converted (for the most part) into a function call instead of switch (e.g., lots of repition)
                                                switch ((Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true))
                                                {
                                                    case Variable.VarType.index:
                                                        globalVariable = Controller.Instance.Z3.MkConst(name, Controller.Instance.IndexType);
                                                        v.Type = Variable.VarType.index;
                                                        globalVariablePrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.IndexType);
                                                        break;
                                                    case Variable.VarType.integer:
                                                        globalVariable = Controller.Instance.Z3.MkConst(name, Controller.Instance.IntType);
                                                        v.Type = Variable.VarType.integer;
                                                        v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                        globalVariablePrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.IntType);
                                                        break;
                                                    case Variable.VarType.real:
                                                        globalVariable = Controller.Instance.Z3.MkConst(name, Controller.Instance.RealType);
                                                        v.Type = Variable.VarType.real;
                                                        v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                        globalVariablePrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.RealType);
                                                        break;
                                                    case Variable.VarType.nnreal:
                                                        globalVariable = Controller.Instance.Z3.MkConst(name, Controller.Instance.RealType);
                                                        v.Type = Variable.VarType.nnreal;
                                                        v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                        globalVariablePrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.RealType);
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
                                                Controller.Instance.Z3.AssertCnstr(Controller.Instance.IntZero <= Controller.Instance.GlobalVariables[v.Name] & Controller.Instance.GlobalVariables[v.Name] <= Controller.Instance.Params["N"]);
                                                Controller.Instance.Z3.AssertCnstr(Controller.Instance.IntZero <= Controller.Instance.GlobalVariablesPrimed[v.Name] & Controller.Instance.GlobalVariablesPrimed[v.Name] <= Controller.Instance.Params["N"]);
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
