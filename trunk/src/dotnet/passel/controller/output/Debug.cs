using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace passel.controller.output
{
    class Debug
    {
        public static uint MINIMAL = 5;
        public static uint VERBOSE_STEPS = 10;
        public static uint VERBOSE_TERMS = 100;

        public static uint VERBOSE_STATS = 200;

        public static uint VERBOSE_ALL = 1000;

        public static uint Level = VERBOSE_STEPS;

        public static void Write(String s)
        {
            Write(s, MINIMAL);
        }

        public static void Write(String s, uint level)
        {
            if (Debug.Level >= level)
            {
                Console.WriteLine(s);
            }
        }
    }
}
