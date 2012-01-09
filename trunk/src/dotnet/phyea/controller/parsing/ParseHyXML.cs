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

                                        String update_type = reader.GetAttribute(VariableAttributes.update_type.ToString()); // todo fix hack: global vars have update type, while parameters don't

                                        Term param = null;
                                        Term paramPrime = null;

                                        switch ((ParameterTypes)Enum.Parse(typeof(ParameterTypes), type, true))
                                        {
                                            case ParameterTypes.index:
                                                param = Controller.Instance.Z3.MkConst(name, Controller.Instance.IndexType);
                                                if (update_type != null)
                                                {
                                                    Variable v = new Variable();
                                                    v.Name = name;
                                                    v.Type = Variable.VarType.index;
                                                    v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                    sys.Variables.Add(v);
                                                    paramPrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.IndexType);
                                                }
                                                break;

                                            case ParameterTypes.integer:
                                                param = Controller.Instance.Z3.MkConst(name, Controller.Instance.IntType);
                                                if (update_type != null)
                                                {
                                                    Variable v = new Variable();
                                                    v.Name = name;
                                                    v.Type = Variable.VarType.integer;
                                                    v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                    sys.Variables.Add(v);
                                                    paramPrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.IntType);
                                                }
                                                break;
                                            case ParameterTypes.real:
                                                param = Controller.Instance.Z3.MkConst(name, Controller.Instance.RealType);
                                                if (update_type != null)
                                                {
                                                    Variable v = new Variable();
                                                    v.Name = name;
                                                    v.Type = Variable.VarType.integer;
                                                    v.UpdateType = (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true);
                                                    sys.Variables.Add(v);
                                                    paramPrime = Controller.Instance.Z3.MkConst(name + "'", Controller.Instance.RealType);
                                                }
                                                break;
                                        }

                                        if (param != null)
                                        {
                                            Controller.Instance.Params.Add(name, param);
                                        }
                                        else
                                        {
                                            throw new System.Exception("Parameter term not created.");
                                        }

                                        if (paramPrime != null)
                                        {
                                            Controller.Instance.ParamsPrimed.Add(name, paramPrime);
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

                                        Property p = new Property(pstr, (Property.PropertyType)Enum.Parse(typeof(Property.PropertyType), type, true));
                                        sys.Properties.Add(p);

                                        break;
                                    }
                                case ElementNames.assumption:
                                    {
                                        String assump = reader.GetAttribute(AssumptionAttributes.equn.ToString());
                                        if (assump.Length > 0)
                                        {
                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(assump);
                                            // assert the assumption
                                            Controller.Instance.Z3.AssertCnstr(LogicalExpression.CreateTerm(tmptree));
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
                                            String[] vns = variable.Split('[');
                                            String variableName = vns[0]; // todo: error handling


                                            Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(flow);
                                            List<String> vars = LogicalExpression.findContinuousVars(tmptree);
                                            List<String> pvars = LogicalExpression.findParams(tmptree);
                                            List<String> constants = LogicalExpression.findAllRealConstants(tmptree);
                                            Term expr = LogicalExpression.CreateTerm(tmptree);
                                            List<Term> flows = new List<Term>();
                                            Term t1 = Controller.Instance.Z3.MkConst("t_1", Controller.Instance.RealType);

                                            // todo: add global variable support, currently assumes indexed

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
                                                    Term c = Controller.Instance.Z3.MkRealNumeral((int)float.Parse(cs));
                                                    Term addDeltaMin = Controller.Instance.IndexedVariables[new KeyValuePair<string, string>(variableName, "i")] + (c * t1);
                                                    Controller.Instance.Z3.replaceTerm(ref expr, expr, c, addDeltaMin, false);
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
                                                    l.Flow = expr;
                                                }
                                            }
                                        }
                                        //todo: set dynamics for location
                                        //r.setRateEqualForVar(varX, real_one);

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
                                        if (h == null)
                                        {
                                            throw new System.Exception("Error parsing transition: hybrid automaton not specified properly before reaching transition.");
                                        }
                                        t = new Transition();

                                        AState from = null; // have to find the frome state as well, because in hyxml syntax, transitions are not associated with locations...
                                        foreach (AState s in h.Locations)
                                        {
                                            // todo: build hash table after found once
                                            try
                                            {
                                                String des = reader.GetAttribute(TransitionAttributes.destination.ToString());
                                                if (s.Label == reader.GetAttribute(TransitionAttributes.destination.ToString()))
                                                {
                                                    t.NextStates.Add(s);
                                                }
                                            }
                                            catch
                                            {
                                                if (s.Value == UInt32.Parse(reader.GetAttribute(TransitionAttributes.destination.ToString())))
                                                {
                                                    t.NextStates.Add(s);
                                                }
                                            }

                                            try
                                            {
                                                if (s.Label == reader.GetAttribute(TransitionAttributes.source.ToString()))
                                                {
                                                    from = s;
                                                }
                                            }
                                            catch
                                            {
                                                if (s.Value == UInt32.Parse(reader.GetAttribute(TransitionAttributes.source.ToString())))
                                                {
                                                    from = s;
                                                }
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


                                        break;
                                    }
                                case ElementNames.variable:
                                    {
                                        if (h == null)
                                        {
                                            throw new System.Exception();
                                        }
                                        String name = reader.GetAttribute(VariableAttributes.name.ToString());
                                        String type = reader.GetAttribute(VariableAttributes.type.ToString());
                                        String update_type = reader.GetAttribute(VariableAttributes.update_type.ToString());
                                        
                                        // todo: generalize to the actual general parser? we don't really want to allow such complex declarations of variables, but why not...?
                                        if (name.Contains("[") && name.Contains("]")) // indexed variable
                                        {
                                            String[] split = name.Split('[', ']');
                                            String varName = split[0];
                                            String indexName = split[1];

                                            h.addIndexedVariable(varName, (Variable.VarType)Enum.Parse(typeof(Variable.VarType), type, true), (Variable.VarUpdateType)Enum.Parse(typeof(Variable.VarUpdateType), update_type, true));
                                            //r.setRateEqualForVar(varX, real_one);
                                            // todo: parse the variables
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
                                                Controller.Instance.Z3.AssertCnstr(Controller.Instance.IntZero <= Controller.Instance.Params[v.Name] & Controller.Instance.Params[v.Name] <= Controller.Instance.Params["N"]);
                                                Controller.Instance.Z3.AssertCnstr(Controller.Instance.IntZero <= Controller.Instance.ParamsPrimed[v.Name] & Controller.Instance.ParamsPrimed[v.Name] <= Controller.Instance.Params["N"]);
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
