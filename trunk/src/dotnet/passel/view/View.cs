using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using passel.model;

namespace passel.view
{
    public partial class View : Form
    {
        public View()
        {
            InitializeComponent();

            
            
        }

        private void panelSystem_Paint(object sender, PaintEventArgs e)
        {
            /*
            //System.Drawing.Graphics g = System.Drawing.Graphics.FromHwnd(this.panelSystem.Handle);
            Graphics g = this.panelSystem.CreateGraphics();
            g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
            System.Drawing.Pen p = new System.Drawing.Pen(System.Drawing.Color.Black);
            System.Drawing.Brush b = new System.Drawing.SolidBrush(System.Drawing.Color.Orange);
            //g.FillEllipse(b, this.panelSystem.Location.X + 50, this.panelSystem.Location.Y + 50, 100, 100);
            g.DrawEllipse(p, this.panelSystem.Location.X + 50, this.panelSystem.Location.Y + 50, 100, 100);*/
        }

        public void drawSystem(Holism h)
        {
            Graphics g = this.panelSystem.CreateGraphics();
            g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
            System.Drawing.Pen p = new System.Drawing.Pen(System.Drawing.Color.Black);
            System.Drawing.Brush b = new System.Drawing.SolidBrush(System.Drawing.Color.Black);

            System.Drawing.Brush bDiff = new System.Drawing.SolidBrush(System.Drawing.Color.Blue);
            System.Drawing.Brush bInv = new System.Drawing.SolidBrush(System.Drawing.Color.Green);
            System.Drawing.Brush bStop = new System.Drawing.SolidBrush(System.Drawing.Color.Red);

            System.Drawing.Brush bGuard = new System.Drawing.SolidBrush(System.Drawing.Color.Green);
            System.Drawing.Brush bUGuard = new System.Drawing.SolidBrush(System.Drawing.Color.Purple);
            System.Drawing.Brush bReset = new System.Drawing.SolidBrush(System.Drawing.Color.Red);

            //g.FillEllipse(b, this.panelSystem.Location.X + 50, this.panelSystem.Location.Y + 50, 100, 100);
            //g.DrawEllipse(p, this.panelSystem.Location.X + 50, this.panelSystem.Location.Y + 50, 100, 100);

            int i = 0;
            int width = 250;
            int height = 150;
            int spacing = (int)((float)width * 1.5);

            Dictionary<string, Point> stateNameToPosition = new Dictionary<string,Point>();

            foreach (ConcreteLocation a in h.HybridAutomata[0].Locations)
            {
                int x = this.panelSystem.Location.X + i*spacing;
                int y = this.panelSystem.Location.Y + 50;

                int xmid = (int)(x + width / 2);
                int ybot = y + height;

                stateNameToPosition.Add(a.Label, new Point(xmid, ybot));

                g.DrawEllipse(p, x, y, width, height);

                g.DrawString(a.Label, new System.Drawing.Font("Arial", 16), b, xmid, y);

                int offset = 20;
                int offset_count = 1;
                int fontsize = 12;
                if (a.Invariant != null)
                {
                    g.DrawString(a.Invariant.ToString(), new System.Drawing.Font("Arial", fontsize), bInv, xmid, y + offset * offset_count++);
                }
                if (a.Stop != null)
                {
                    g.DrawString(a.Stop.ToString(), new System.Drawing.Font("Arial", fontsize), bStop, xmid, y + offset * offset_count++);
                }
                if (a.Flows != null && a.Flows.Count > 0)
                {
                    g.DrawString(a.Flows[0].ToString(), new System.Drawing.Font("Arial", fontsize), bDiff, xmid, y + offset * offset_count++);
                }

                i++;
            }

            // separate loop, need stateNameToPosition created
            foreach (ConcreteLocation a in h.HybridAutomata[0].Locations)
            {
                int ct = 1;
                foreach (Transition t in a.Transitions)
                {
                    foreach (ConcreteLocation next in t.NextStates)
                    {
                        List<Point> pts = new List<Point>();

                        Point start = stateNameToPosition[a.Label];
                        Point end = stateNameToPosition[next.Label];
                        Point midpoint = new Point(Math.Abs(start.X + end.X) / 2, start.Y + ct * 2 * height);

                        pts.Add(start);
                        pts.Add(midpoint);
                        pts.Add(end);
                        g.DrawCurve(p, pts.ToArray());

                        int offset = 20;
                        int offset_count = 1;
                        int fontsize = 12;
                        if (t.Guard != null)
                        {
                            g.DrawString(t.Guard.ToString(), new System.Drawing.Font("Arial", fontsize), bGuard, midpoint.X, midpoint.Y + offset * offset_count++);
                        }
                        if (t.UGuard != null)
                        {
                            g.DrawString(t.UGuard.ToString(), new System.Drawing.Font("Arial", fontsize), bUGuard, midpoint.X, midpoint.Y + offset * offset_count++);
                        }
                        if (t.Reset != null)
                        {
                            g.DrawString(t.Reset.ToString(), new System.Drawing.Font("Arial", fontsize), bReset, midpoint.X, midpoint.Y + offset * offset_count++);
                        }
                        ct++;
                    }
                }
            }
        }

        private void label1_Click(object sender, EventArgs e)
        {

        }
    }
}
