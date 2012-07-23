using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

using passel.model;

namespace passel.controller.output
{
    public class PrintPhaver
    {
        public enum OutputMode { phaver };

        /**
         * Print the transition system to appropriate output format specified by m
         */
       /* public static void writeAbstractSystem(AbstractHybridAutomaton aha, String filename, OutputMode m)
        {
            String path = System.IO.Directory.GetCurrentDirectory() + System.IO.Path.DirectorySeparatorChar.ToString();

            StreamWriter sw = new StreamWriter(filename);

            switch (m)
            {
                case OutputMode.phaver:
                    {

                        sw.WriteLine("automaton default_automaton" + Environment.NewLine);
                        sw.WriteLine("state_var:");
                        // todo: if using timers, iterate through all the variables and print them here
                        sw.WriteLine("\tt;" + Environment.NewLine); // add a timer

                        // todo: if we have synchronization, add the labels here
                        sw.WriteLine("synclabs: dummy;" + Environment.NewLine); // add a dummy synchronization label (necessary for phaver syntax)

                        // print some comments to indicate what each abstract state represents
                        int i = 0;

                        //foreach (aha.States.First().ReferenceState.

                        foreach (EnvironmentState e in aha.States.First().EnvironmentStates)
                        {
                            sw.WriteLine("// E_" + i.ToString() + ": " + e.ToString());
                            i++;
                        }
                        sw.WriteLine();// newline

                        sw.WriteLine("// r = " + aha._r);
                        sw.WriteLine("// S = " + aha._S);
                        sw.WriteLine("// T = " + aha._T);
                        sw.WriteLine();
                        sw.WriteLine("// # valuations (total): " + Math.Pow(2, aha._S) * Math.Pow(2, aha.Valuations.First().EnvironmentStates.Count - 1));
                        sw.WriteLine("// # valuations (pruned): " + aha.Valuations.Count);
                        sw.WriteLine();

                        foreach (AbstractState s in aha.Valuations)
                        {
                            sw.WriteLine("// " + s.Concretization().ToString().Replace(System.Environment.NewLine, "").Replace("\n", "").Replace("\r", "").Replace("  ", ""));
                            sw.Write("loc " + s.ToString() + ": ");
                            sw.WriteLine("while true wait {t' == 0 };");
                            // todo: iterate over all the transitions and print them here as roughly
                            sw.WriteLine("\t// number of transitions out: " + s.Transitions.Count);
                            foreach (Transition t in s.Transitions)
                            {
                                foreach (AState l in t.NextStates)
                                {
                                    sw.WriteLine("\twhen true sync dummy goto " + l.ToString() + "; // " + t.Type.ToString() + " transition");
                                }
                            }
                        }
                        sw.Write(Environment.NewLine + Environment.NewLine);

                        // initial states (any state)
                        //todo: only allow valid initial states
                        sw.WriteLine("initially: flying1000 & true;");
                        sw.Write(Environment.NewLine + Environment.NewLine);

                        sw.WriteLine("end");

                        sw.WriteLine("sys = default_automaton; // copy, modify the other one");
                        sw.WriteLine("reachset = sys.reachable;");
                        sw.WriteLine("reachset.print(\"" + path + filename + "_reach\", 0);");
                        sw.WriteLine("echo \"\";");
                        sw.WriteLine("echo \"Reachable states:\";");
                        sw.WriteLine("reachset.print;");
                        sw.WriteLine("badset=default_automaton.{runway0001 & True};"); // todo: find bad set of states
                        sw.WriteLine("reachset.intersection_assign(badset);");
                        sw.WriteLine("echo \"\";");
                        sw.WriteLine("echo \"Forbidden states:\";");
                        sw.WriteLine("badset.print;");
                        sw.WriteLine("echo \"\";");
                        sw.WriteLine("echo \"Reachable forbidden states:\";");
                        sw.WriteLine("reachset.print;");
                        sw.WriteLine("echo \"\";");
                        sw.WriteLine("echo \"Reachable forbidden states empty?\";");
                        sw.WriteLine("reachset.is_empty;");

                        break;
                    }
            }

            sw.Close();
        }*/
    }
}
