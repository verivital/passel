using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace passel.controller.parsing
{
    class ParsePhaverOutput
    {

        /// <summary>
        /// Parse phaver reach set files
        /// </summary>
        /// <param name="path"></param>
        /// <param name="replaceIndices"></param>
        /// <returns></returns>
        public static List<String> ParseReach(String path, bool replaceIndices)
        {
            //List<Expr> reach = new List<Expr>();
            List<String> reach = new List<String>();

            if (!File.Exists(path))
            {
                Console.WriteLine("Error: reach set file not found.\n\r");
                return reach;
            }

            StreamReader reader = new StreamReader(path);

            String reachset = reader.ReadToEnd();
            String reachset_entire = "";
            String forall = "";
            String exists = "";

            reachset = reachset.Substring(reachset.IndexOf("{"));

            String reachstate = "";
            int count = 0;
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
                if (count == 0)
                {
                    reachstate = reachset.Substring(start + 1, end - (start + 1));
                }
                else
                {
                    reachstate = reachset.Substring(start + 1, end - (start));
                }
                reachstate = reachstate.Replace("\n", "");
                reachstate = reachstate.Replace("\r", "");
                reachstate = reachstate.Replace("&", "&&");
                reachstate = reachstate.Replace("|", "||");
                //reachstate = reachstate.Replace(" < ", " <= "); // TODO: HUGE HACK: THIS IS THE "CLOSURE" OPERATOR
                //reachstate = reachstate.Replace(" > ", " >= "); // TODO: HUGE HACK: THIS IS THE "CLOSURE" OPERATOR
                reachstate = reachstate.Trim();
                reachstate = reachstate.TrimStart('(', ',', '}', '{'); // strip parentheses and commas
                reachstate = reachstate.TrimEnd(')', ',', '}', '{');
                string vt = "[\\-_a-zA-Z0-9\\s]+"; // variable or number
                string mid = "[\\-_a-zA-Z0-9\\s\\+\\(\\)\\*\\\\]+"; // linear arithmetic over variables or numbers: TODO: WHAT IF DECIMAL? IS IT POSSIBLE, OR ARE ALL RATIONALS?
                string ineq = ">=|&gt;=|<=|&lt;=|>|&gt;|<|&lt;";
                Regex rineq = new Regex("((" + vt + ")(" + ineq + ")(" + mid + ")(" + ineq + ")(" + vt + "))");
                MatchCollection mc = rineq.Matches(reachstate);

                foreach (var m in mc)
                {
                    string[] splits = m.ToString().Split(new String[] { ">=", "&gt;=", ">", "&gt;", "<=", "&lt;=", "<", "&lt;" }, StringSplitOptions.None);
                    string newstr = m.ToString().Replace(splits[1], splits[1] + " && " + splits[1]);
                    reachstate = reachstate.Replace(m.ToString(), newstr);
                }

                /*
                string rel = ">=|&gt;=|<=|&lt;=|>|&gt;|<|&lt;|==";
                Regex rrel = new Regex("((" + mid + ")(" + rel + ")(" + mid + "))");
                mc = rrel.Matches(reachstate);

                foreach (var m in mc)
                {
                    
                    reachstate = reachstate.Replace(m.ToString(), newstr);
                }
                 */

                reachstate = Regex.Replace(reachstate, "(?<!\\B|\\.)(\\d+)(?!\\.\\d+)\\b", "$1.0"); // replace all integers by floats; TODO: CHECK GENERALITY




                /*
                string rel = ">=|&gt;=|<=|&lt;=|>|&gt;|<|&lt;|==";
                Regex rrel = new Regex("((" + mid + ")(" + rel + ")(" + mid + "))");
                mc = rrel.Matches(reachstate);

                foreach (var m in mc)
                {
                    string[] splits = m.ToString().Split(new String[] { ">=", "&gt;=", ">", "&gt;", "<=", "&lt;=", "<", "&lt;", "==", "+", "\\", "*", "/" }, StringSplitOptions.None);

                    bool hasreal = false;
                    foreach (var v in splits)
                    {
                        string k = v.Trim();
                        if (Controller.Instance.DataU.IndexedVariableDecl.ContainsKey(k) && Controller.Instance.DataU.IndexedVariableDecl[k].Range == Controller.Instance.RealType)
                        {
                            hasreal = true;
                            break;
                        }
                    }

                    string newstr = "";
                    if (hasreal)
                    {
                        foreach (var v in splits)
                        {
                            string k = v.Trim();
                            int tmp;
                            if (int.TryParse(k, out tmp))
                            {

                            }
                            else
                            {
                                newstr += " " + k;
                            }
                        }
                    }
                    //string newstr = m.ToString() + splits[1];
                    //string newstr = m.ToString().Replace(splits[1], splits[1] + " && " + splits[1]);
                    
                    reachstate = reachstate.Replace(m.ToString(), newstr);
                }*/

                //reachstate = rineq.Replace(reachstate, ((char)idx).ToString());

                if (count == 0)
                {
                    //reachstate = reachstate.Substring(1, reachstate.Length - 2); // remove parentheses
                }
                else
                {
                    //reachstate = reachstate.Substring(0, reachstate.Length - 1); // remove parentheses
                }


                // nasty hack: add decimal zero behind all numbers (to make them be parsed as reals)
                /*
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
                reachstate = reachstatereal;*/

                for (uint i = 0; i <= Controller.Instance.IndexNValue; i++)
                {
                    // TODO: add function to convert index integer to index symbol (e.g., wrap-around after hitting z, or some other value, and start making indices like ii, ij, ik, ..., iii, iij, etc.)
                    uint idx = 'i' + i;
                    if (replaceIndices)
                    {
                        reachstate = reachstate.Replace("_" + (i + 1), "[" + (char)idx + "]"); // add integer to char to get next index (temporary)
                        //reachstate = reachstate.Replace("_2", "[j]");
                        //reachstate = reachstate.Replace("_3", "[k]");

                        Regex r = new Regex("\\b[" + (i + 1).ToString() + "]\\b");
                        reachstate = r.Replace(reachstate, ((char)idx).ToString());
                        //reachstate = reachstate.Replace((i+1).ToString(), ((char)idx).ToString()); // TODO: GENERALIZE, THIS IS HORRIBLE, NEED SPECIAL NAMES FOR PROCESS INDICES OR SOMETHING, PERHAPS CONSTANTS AT TOP? BUT REACH SET WILL STILL BE VERY DIFFICULT...MAYBE USE PRIME CONSTANTS?... SOMEHOW HAVE TO MAP BACK FROM CONCRETE IDS TO I,J,K,...
                    }
                    else
                    {
                        //reachstate = reachstate = reachstate.Replace("_" + (i + 1), "[" + (i + 1) + "]"); // convert _1 to [1]
                        reachstate = reachstate = reachstate.Replace("_" + (i + 1), (i + 1).ToString()); // convert _1 to [1]
                    }
                }

                String loc = reachset.Substring(0, start - 1);
                loc = loc.Trim();
                loc = loc.Trim('{', '}', ',');
                // assume 1st state is for global automaton

                String[] locs = loc.Split('~');

                loc = "";
                forall = "forall ";
                exists = "exists ";

                bool locsame = true;

                int globals = 0;
                if (locs.Contains("default"))
                {
                    globals++; // todo: use predicate
                }

                for (uint i = 0; i < Controller.Instance.IndexNValue; i++)
                {
                    uint idx = 'i' + i;
                    locs[i + globals] = locs[i + globals].Replace("{", "");
                    locs[i + globals] = locs[i + globals].Replace("}", "");
                    locs[i + globals] = locs[i + globals].Trim();

                    //string locstr = "#b" +  Convert.ToString(Controller.Instance.LocationNameToNum[locs[i + 1]], 2).PadLeft((int)Controller.Instance.LocSize, '0'); // convert integer to bitvector string
                    string locstr = "#b" + Controller.Instance.LocationNameToNum[locs[i + globals]];
                    if (replaceIndices)
                    {
                        //TODO: was locstr
                        loc += "(q[" + (char)idx + "] == " + locs[i + globals] + ") && "; // i + 1 to skip global arbiter automaton's state (always listed first)
                    }
                    else
                    {
                        //loc += "(q[" + (i + 1) + "] == " + locs[i + 1] + ") && "; // i + 1 to skip global arbiter automaton's state (always listed first)
                        //TODO: was locstr
                        loc += "(q" + (i + 1) + " == " + locs[i + globals] + ") && "; // i + 1 to skip global arbiter automaton's state (always listed first)
                    }
                    forall += (char)idx + " ";
                    exists += (char)idx + " ";
                    if (i >= 1)
                    {
                        locsame &= locs[i] == locs[i + globals];
                    }
                }
                loc = loc.Substring(0, loc.Length - 4); // remove last and


                List<String> disj = reachstate.Split(new string[] { "||" }, StringSplitOptions.RemoveEmptyEntries).ToList();

                bool splitLocDisjuncts = true;

                string tmpdisj = "";
                foreach (var d in disj)
                {
                    // add full disjunctive formula
                    if (replaceIndices || !splitLocDisjuncts)
                    {
                        tmpdisj += "(" + d + ")" + " || ";

                        //reach.Add(forall + "(((" + loc + ")) and (" + reachstate + "))");
                        //reach.Add(forall + "(((" + loc + ")) implies (" + d + "))");
                        //reach.Add(forall + "( ((" + reachstate + ")) implies (" + loc + "))");
                    }
                    else
                    {
                        //reach.Add("(" + loc + " and (" + reachstate + "))");
                        reach.Add("(" + loc + " implies (" + d + "))");

                        //reach.Add("( (" + reachstate + ") implies (" + loc +"))");
                        //reach.Add("(" + loc + " iff (" + reachstate + "))");
                    }
                }

                if (!splitLocDisjuncts)
                {
                    //reach.Add(forall + "(((" + loc + ")) implies (" + tmpdisj.Substring(0, tmpdisj.Length - 4) + "))");
                    reach.Add("(((" + loc + ")) implies (" + tmpdisj.Substring(0, tmpdisj.Length - 4) + "))");
                }


                /*

                // add full disjunctive formula
                if (replaceIndices)
                {
                    //reach.Add(forall + "(((" + loc + ")) and (" + reachstate + "))");
                    reach.Add(forall + "(((" + loc + ")) implies (" + reachstate + "))");
                    //reach.Add(forall + "( ((" + reachstate + ")) implies (" + loc + "))");
                }
                else
                {
                    //reach.Add("(" + loc + " and (" + reachstate + "))");
                    reach.Add("(" + loc + " implies (" + reachstate + "))");

                    //reach.Add("( (" + reachstate + ") implies (" + loc +"))");
                    //reach.Add("(" + loc + " iff (" + reachstate + "))");
                }*/

                /*
                String allVars = "";
                foreach (var v in Controller.Instance.IndexedVariables.Keys)
                {
                    allVars = v.Key + "[" + v.Value + "]";
                }
                // project
                reach.Add(exists + "(((" + loc + ")) implies (" + reachstate + "))");
                 */

                /*
                if (reachstate.Contains("|"))
                {
                    // split into many disjuncts
                    String[] reachstate_disj = reachstate.Split(new string[] { "||" }, StringSplitOptions.None);
                    foreach (var v in reachstate_disj)
                    {
                        reachstate = "(((" + loc + ")) implies (" + v + "))"; // todo: generalize > 2
                        reachstate = forall + reachstate;
                        reach.Add(reachstate);
                    }
                }*/


                //reachstate = forall + "(((" + loc + (Controller.Instance.IndexNValue > 1 ? (locsame ? " && i == j" : " && i != j " ) : "") + ")) implies (" + reachstate + "))"; // todo: generalize > 2
                //reachstate = forall + "(((" + loc + ")) implies (" + reachstate + "))"; // todo: generalize > 2
                //reachstate = "(((" + loc + ")) implies (" + reachstate + "))" + " && "; // todo: generalize > 2
                //reachstate = "(((" + loc + ")) implies (" + reachstate + "))"; // todo: generalize > 2

                //reachset_entire += reachstate + " || ";

                //reachstate = forall + reachstate;

                //Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(reachstate);
                //Expr rs = LogicalExpression.CreateTerm(tmptree);
                //reach.Add(rs);
                //reach.Add(reachstate);

                reachset = reachset.Substring(end + 1); // cut off from reachset
                count++;
            } while (reachset.Length > 0 || reachset.Contains(","));

            // remove duplicates, if any
            reach = reach.Distinct().ToList();

            //reachset_entire = forall + "(" + reachset_entire.Substring(0, reachset_entire.Length - 4) + ")"; // remove last and; add forall
            //Antlr.Runtime.Tree.CommonTree tmptree = math.Expression.Parse(reachset_entire);

            //Expr rs = LogicalExpression.CreateTerm(tmptree);

            //reach.Add(rs);
            //reach.Add(reachset_entire);


            return reach;
        }
    }
}
