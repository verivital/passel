using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace passel.model
{
    /**
     * Quotient space of natural numbers defined by a cut at N and at a pre-specified maximum value
     * 
     * Example: N is arbitrary, but we assume N > N - 1 > Cutoff, for Cutoff >= 1, so N is at least 3
     * 
     * Any addition to a value greater than N yields N
     * 
     * Any subtraction from a value less than 0 yields 0
     * 
     */
    public class Counter
    {
        public static uint MaxValue = 1; // todo: any way to parameterize this? can't seem to do it with generics, but also can't pass it via constructor it as we need it to be static it
        public uint Value;

        public Counter(uint val)
        {
            this.Value = val;
        }

        public static Counter None = new Counter(0);            // 0
        public static Counter One = new Counter(1);             // 1
        public static Counter Cutoff = new Counter(MaxValue);   // counter cutoff value: 1 == existential, 2 == can track states of 2 processes, etc.
        public static Counter AllButOne;  // N - 1
        public static Counter All;        // N

        /**
         * Overload addition
         */
        public static Counter operator +(Counter c1, Counter c2)
        {
            uint v = c1.Value + c2.Value;
            if (v >= MaxValue)
            {
                return Cutoff;
            }
            else
            {
                return new Counter(v);
            }
        }

        /**
         * Overload subtraction
         */
        public static Counter operator -(Counter c1, Counter c2)
        {
            uint v = c1.Value - c2.Value;
            if (v <= 0)
            {
                return None;
            }
            else
            {
                return new Counter(v);
            }
        }

        /**
         * Overload unary minus
         */
        public static Counter operator -(Counter c1)
        {
            return None - c1;
        }

        /**
         * Overload increment
         */
        public static Counter operator ++(Counter c1)
        {
            return c1 + Counter.One;
        }

        /**
         * Overload increment
         */
        public static Counter operator --(Counter c1)
        {
            return c1 - Counter.One;
        }

        /**
         * Overload comparison
         * 
         * Could do this recursively and it would be quite elegant, but also probably very slow
         */
        public static Boolean operator >(Counter c1, Counter c2)
        {
            if (c1 == All && c2 != All)
            {
                return true;
            }

            if (c1 == AllButOne && c2 != All && c2 != AllButOne)
            {
                return true;
            }

            if (c2 == All || c2 == AllButOne)
            {
                return false;
            }

            return (c1.Value > c2.Value); // do the integer comparison
        }

        /**
         * Overload comparison
         * 
         */
        public static Boolean operator <(Counter c1, Counter c2)
        {
            return !(c1 >= c2);
        }

        /**
         * Overload comparison
         */
        public static Boolean operator >=(Counter c1, Counter c2)
        {
            if (c1 == All)
            {
                return true;
            }

            if (c1 == AllButOne && c2 != All)
            {
                return true;
            }

            if (c2 == All || c2 == AllButOne)
            {
                return false;
            }

            return (c1.Value >= c2.Value); // do the integer comparison
        }

        /**
         * Overload comparison
         * 
         */
        public static Boolean operator <=(Counter c1, Counter c2)
        {
            return !(c1 > c2);
        }
    }
}
