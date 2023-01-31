__all__ = ['RF']

import plotly.graph_objects as go
import math
import sys

class Resource_fig():
    def __init__(self, LUT_type, scq_size, target_timestamp):
        if (LUT_type not in ('3', '4', '6')):
            print("Error in selecting LUT type.")
            return
        self.LUT_type = LUT_type
        self.tot_scq = scq_size
        self.tts = target_timestamp
        self.fig1 = go.Figure()
        self.fig2 = go.Figure()

    def config(self, LUT_type, scq_size, target_timestamp):
        self.LUT_type = LUT_type
        self.tot_scq = scq_size
        self.tts = target_timestamp

    def gen_comparator(self, width,k):
        if(k==3):
            return 4*width+1
        if(k==4):
            return 2*width+1
        elif(k==6):
            return width+1
        return -1

    def gen_adder(self, width,k):
        if(k==6):
            return width
        elif(k==4):
            return width*2
        elif(k==3):
            return width*2
        else:
            return -1

    def gen_LUT_fig(self):
        self.fig1 = go.Figure()
        st = max(self.tts-40, 0)
        ed = self.tts+30
        x = list(range(st, ed, 1))

        y_3,y_4,y_6=[],[],[]
        z_3,z_4,z_6=[],[],[]
        tot_comp = 33
        tot_add = 32
        for data in x:
            y_3.append(self.gen_comparator(data,3)*tot_comp)
            y_4.append(self.gen_comparator(data,4)*tot_comp)
            y_6.append(self.gen_comparator(data,6)*tot_comp)
            z_3.append(self.gen_adder(data,3)*tot_add)
            z_4.append(self.gen_adder(data,4)*tot_add)
            z_6.append(self.gen_adder(data,6)*tot_add)
        y_1, y_2, name_1, name_2 = [],[],"",""
        if (self.LUT_type=='3'):
            y_1, y_2 = y_3, z_3
            name_1 = "Number of LUT-3 for all Comparators"
            name_2 = "Number of LUT-3 for all Adder/Subtractors"
        elif (self.LUT_type=='4'):
            y_1, y_2 = y_4, z_4
            name_1 = "Number of LUT-4 for all Comparators"
            name_2 = "Number of LUT-4 for all Adder/Subtractors"
        else:
            y_1, y_2 = y_6, z_6
            name_1 = "Number of LUT-6 for all Comparators"
            name_2 = "Number of LUT-6 for all Adder/Subtractors"
        

        self.fig1.update_layout(title='Number of LUTs',
               xaxis_title='Timestamp Width (bits)',
               yaxis_title='Future-Time Number of LUTs')

        # dash options include 'dash', 'dot', and 'dashdot'
        self.fig1.add_trace(go.Scatter(x=x, y=y_1, name=name_1,
                     line=dict(color='firebrick', width=4)))
        self.fig1.add_trace(go.Scatter(x=x, y=y_2, name = name_2,
                                 line=dict(color='royalblue', width=4)))
        self.fig1.add_trace(go.Scatter(x=[self.tts, self.tts],y=[y_1[self.tts-st], y_2[self.tts-st]], 
            name = "Current Configuration", line = dict(width=0),
                                line_shape = 'vhv'))

    def gen_BRAM_fig(self):
        self.fig2 = go.Figure()
        dep_tab = {1:16384,2:8192,4:4096,9:2048,18:1024,36:256}
        def gen_bram(nt,width):
            if(width<=36):
                cand = sys.maxsize # 88
                for key, value in dep_tab.items():
                    if(key>=width):
                        cand = min(cand,key)
                        break
                return math.ceil(nt/dep_tab[cand])
            else:
                cand = sys.maxsize #88
                for key, value in dep_tab.items():
                    if(key>=width%36):
                        cand = min(cand,key)
                        break
                return math.ceil(nt/dep_tab[36])*(width//36)+math.ceil(nt/dep_tab[cand])
        st = max(self.tts-40, 0)
        ed = self.tts+30
        x = list(range(st, ed, 1))
        y = []
        for width in x:
            extra = 5+1
            if(width>36):
                extra = 6+1
            # y.append(gen_bram(self.tot_scq ,width)+extra)
            y.append(gen_bram(self.tot_scq, width)+extra)

        self.fig2.update_layout(title='Number of 18Kb BRAMs',
               xaxis_title='Timestamp Width (bits)',
               yaxis_title='Number of 18Kb BRAMs')

        self.fig2.add_trace(go.Scatter(x=x, y=y,
                     line=dict(color='orange', width=4)))

        self.fig2.add_trace(go.Scatter(x=[self.tts,], y=[y[self.tts-st],], name = "Current Configuration",
                     line=dict(color='purple', width=0), line_shape = 'vhv'))

    def get_LUT_fig(self):
        self.gen_LUT_fig()
        return self.fig1
    
    def get_BRAM_fig(self):
        self.gen_BRAM_fig()
        return self.fig2

RF = Resource_fig('3', 100, 32)