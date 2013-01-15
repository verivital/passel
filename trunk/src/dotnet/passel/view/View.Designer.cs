namespace passel.view
{
    partial class View
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.panelSystem = new System.Windows.Forms.Panel();
            this.SuspendLayout();
            // 
            // panelSystem
            // 
            this.panelSystem.AutoScroll = true;
            this.panelSystem.AutoSize = true;
            this.panelSystem.BackColor = System.Drawing.SystemColors.MenuHighlight;
            this.panelSystem.Location = new System.Drawing.Point(12, 41);
            this.panelSystem.MaximumSize = new System.Drawing.Size(1700, 1100);
            this.panelSystem.MinimumSize = new System.Drawing.Size(1700, 1100);
            this.panelSystem.Name = "panelSystem";
            this.panelSystem.Size = new System.Drawing.Size(1700, 1100);
            this.panelSystem.TabIndex = 0;
            this.panelSystem.Paint += new System.Windows.Forms.PaintEventHandler(this.panelSystem_Paint);
            // 
            // View
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.AutoScroll = true;
            this.AutoSize = true;
            this.ClientSize = new System.Drawing.Size(871, 541);
            this.Controls.Add(this.panelSystem);
            this.Name = "View";
            this.Text = "View";
            this.WindowState = System.Windows.Forms.FormWindowState.Maximized;
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        public System.Windows.Forms.Panel panelSystem;
    }
}