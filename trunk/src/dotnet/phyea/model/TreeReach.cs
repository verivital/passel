using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace phyea.model
{
    public class TreeReach
    {
        List<TreeReach> _children;
        Term _formula;

        public TreeReach(Term formula, List<Term> childTerms)
        {
            this._formula = formula;

            if (childTerms != null)
            {
                this._children = new List<TreeReach>();
                foreach (var term in childTerms)
                {
                    this._children.Add(new TreeReach(term, null));
                }
            }
        }

        public List<TreeReach> Children
        {
            get
            {
                if (this._children == null)
                {
                    this._children = new List<TreeReach>();
                }
                return this._children;
            }
            set { this._children = value; }
        }

        public Term Formula
        {
            get { return this._formula; }
            set { this._formula = value; }
        }

        public void addChild(Term formula)
        {
            if (this._children == null)
            {
                this._children = new List<TreeReach>();
            }

            this._children.Add(new TreeReach(formula, null));
        }

    }
}
