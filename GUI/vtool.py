#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# pip install dash-cytoscape==0.1.1
# 
# type: ignore
import json
import dash
from dash import html, dcc
import dash_cytoscape as cyto
from dash.dependencies import Input, Output
from textwrap import dedent as d

import plotly.graph_objects as go
from compiler.compiler import compile
from compiler.ast import *
import data_process

cyto.load_extra_layouts()

app = dash.Dash(__name__)
server = app.server

app.title = "R2U2 Resource Estimator"
default_stylesheet = [
    {
        'selector': '[type = "Signal"]',
        'style': {
            'background-color': '#ff9900',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "Bool"]',
        'style': {
            'background-color': '#BFD7B5',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "LogicalNegate"]',
        'style': {
            'background-color': '#66ff99',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "Global"]',
        'style': {
            'background-color': '#6699ff',
            'label': 'data(name)',
        }
    },
    {
        'selector': '[type = "LogicalAnd"]',
        'style': {
            'background-color': '#ff6666',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "Until"]',
        'style': {
            'background-color': '#cc00cc',
            'label': 'data(name)'
        }
    },
    {
        'selector': 'edge',
        'style': {
            'curve-style': 'bezier',
            'target-arrow-color': 'black',
            'target-arrow-shape': 'vee',
            'line-color': 'black'
        }
    }
]

styles = {
    'json-output': {
        'overflow-y': 'scroll',
        'height': 'calc(50% - 25px)',
        'border': 'thin lightgrey solid'
    },
    'tab': {'height': 'calc(98vh - 115px)'},
}

app.layout = html.Div(

    children = [
################title
    html.Div(
        [html.H1('R2U2 Resource Estimator')],
        className = 'row',
        style = {'textAlign':'center'}
        ),

############### left view
    html.Div(
        className = 'row',
        children= [
            html.Div(
                className = 'two columns',
                children = [
                    dcc.Markdown(d("""
                            ###### C2PO Input
                            """)),
                    # dcc.Input(id='formula', value='a0 U[5] a1; a1&a3;', type='text'),
                    dcc.Textarea(
                        id='formula',
                        value='INPUT\n\ta0, a1, a2: bool;\n\nDEFINE\n\ta3 = a0 && a1;\n\nSPEC\n\ta0;\n\ta0 U[0,5] a2;\n\tG[1,3] a3;' ,
                        style={'width': '100%', 'height': '350px'},
                    ),
                    dcc.Checklist(
                        id = 'optimization',
                        options=[
                            {'label': 'Common Subexpression Elimination', 'value': 'opt_cse'},
                        ],
                        value=['opt_cse',]
                    ),
                    html.Pre(id='compile_status', style = {'color': 'blue'}),

                    html.Div(
                        # className = 'one column',
                        style = {'height': '350px'},
                        children=[
                            dcc.Markdown(d("""
                                    ###### C2PO Logging Output
                                    """)),
                            html.Pre(
                                id='compile_output',
                                style=styles['json-output'],
                            )
                        ]
                    ),
                    ],
                    
                ),

                html.Div(
                    className = 'two columns',
                    children = [

                    html.Div(
                            style={'backgroundColor': '#A2F0E4'},
                            children = [
                                dcc.Markdown(d("---\n### Software Configuration")),
                                # Command exection time for each operator
                                dcc.Markdown(d("**TL Clock Cycles**")),
                                dcc.Input(style={'backgroundColor': '#A2F0E4'}, id='op_exe_time', value='10', type='text', size='5'),
                                # Processing time for each atomic checker
                                dcc.Markdown(d("**BZ Clock Cycles**")),
                                dcc.Input(style={'backgroundColor': '#A2F0E4'}, id='at_exe_time', value='10', type='text', size='5'),

                                dcc.Markdown(d("**Clock Frequency (GHz)**")),
                                dcc.Input(style={'backgroundColor': '#A2F0E4'}, id='cpu_clk', value='10', type='text', size='5'),
                                dcc.Markdown(d("**Worst-case Execution Time**")),
                                html.Div(id="comp_speed_CPU",),
                                dcc.Markdown(d("**Total Memory usage for SCQ**")),
                                html.Div(id="tot_memory",),
                            ]
                        ),
                    ]
                ),



                html.Div(
                className = 'two columns',
                children = [
                    html.Div(
                        style={'backgroundColor': '#F7FAC0'},
                        children  = [
                        dcc.Markdown(d("---\n### Hardware Configuration")),
                        dcc.Markdown(d("**Clock Frequency (MHz)**")),
                        dcc.Input(style={'backgroundColor': '#F7FAC0'},id='hardware_clk', value='100', type='text', size='5'),
                        dcc.Markdown(d("**LUT Type Select**")),
                        dcc.Dropdown(
                            id = 'LUT_type',
                            style={'backgroundColor': '#F7FAC0'},
                            options=[
                                {'label': 'LUT-3', 'value': '3'},
                                {'label': 'LUT-4', 'value': '4'},
                                {'label': 'LUT-6', 'value': '6'},
                            ],
                            value='3',
                            clearable=False
                        ),
                        dcc.Markdown(d("**Resource to Observe**")),
                        dcc.Dropdown(
                            id = 'resource_type',
                            style={'backgroundColor': '#F7FAC0'},
                            options=[
                                {'label': 'LUT', 'value': 'LUT'},
                                {'label': '18Kb BRAM', 'value': '18kbBRAM'},
                            ],
                            value='LUT',
                            clearable=False
                        ),  

                        dcc.Markdown(d("**Timestamp Length (Bits)**")),
                        dcc.Input(style={'backgroundColor': '#F7FAC0'},id='timestamp_length', value='32', type='text', size='5'),
                        # dcc.Slider(
                        #     id='timestamp_length',
                        #     min=0,
                        #     max=64,
                        #     step=1,
                        #     value=32,
                        #     marks=None
                        # ),
                        # html.Div(style="width:500px;height:100px;border:1px solid #000;"),
                        # html.Div(id='slider-output-container-ts'),
                        # dcc.Input(id='timestamp_length', value='32', type='text'),
                        html.Div(
                        # style={'backgroundColor': '#A2F0E4'},
                        children = [
                            # dcc.Markdown(d("---\n### Results for Timing and Resource")),
                            dcc.Markdown(d("**Worst-case Execution Time**")),
                            html.Div(id="comp_speed_FPGA",),
                            dcc.Markdown(d("**Total SCQ Memory Slots**")),
                            html.Div(id="tot_scq_size",),
                        ]
                    ),


                        ],
                    ),
                ],
                # style={'width': '15%'}
            ),

            html.Div(
                className = 'four columns',
                children = [
                    cyto.Cytoscape(
                        id='tree',
                        # layout={'name': 'circle'},
                        layout={'name': 'klay','klay': {'direction': 'DOWN'}},
                        stylesheet=default_stylesheet,
                        style={'width': '100%', 'height': '350px'},
                        elements=[]
                    ),
                    dcc.Graph(
                        id='resource_usage',
                        figure = go.Figure(),
                        style={'width': '100%'},
                    )
                ],
                # style={'width': '30%'}
            ),


            html.Div(
                className = 'two columns',
                # style = {'height': '500px'},
                children = [
                    html.Div(
                        # className = 'one column',
                        style = {'height': '300px'},
                        children=[
                        dcc.Markdown(d("#### Mouseover Data")),
                        html.Pre(
                            id='mouseover-node-data-json-output',
                            # style=styles['json-output']
                        )
                        ]
                    ),
                    html.Div(
                        # className = 'one column',
                        style = {'height': '750px'},
                        children=[
                            dcc.Markdown(d("#### Assembly")),
                            html.Pre(
                                id='assembly_window',
                                style=styles['json-output'],
                            )
                        ]
                    ),
                
                ],

            )
        ],  
    ),
])

# @app.callback(
#     Output('slider-output-container-ts', 'children'),
#     [Input('timestamp_length', 'value')])
# def update_output(value):
#     return 'You have selected "{}" bit'.format(value)

# @app.callback(Output('mouseover-edge-data-json-output', 'children'),
#               [Input('tree', 'mouseoverEdgeData')])
# def displayMouseoverEdgeData(data):
#     return json.dumps(data, indent=2)

@app.callback(
    Output('mouseover-node-data-json-output', 'children'),
    [Input('tree', 'mouseoverNodeData')])
def displayMouseoverNodeTitle(data):
    if (data==None or 'bpd' not in data):
        return html.Pre('None Selected')
    return html.Pre(
        'Expression: '+str(data['str'])+'\n'
        +'Node: '+str(data['name'])+'\n'
        +'BPD: '+str(data['bpd'])+'\n'
        +'WPD: '+str(data['wpd'])+'\n'
        +'SCQ size: '+str(data['scq_size'])+'\n'
        )


# @app.callback(Output('selected-node', 'children'),
#               [Input('tree', 'mouseoverNodeData')])
# def displayMouseoverNodeData(data):
#     if (data==None or 'num' not in data):
#         return html.P('Selected Node: NA')
#     return html.P('Selected Node: '+str(data['str']))


def speed_unit_conversion(clk):
    if clk <= 0:
        comp_speed = "Error: Clock speed must be > 0!"
    elif clk<1000:
        comp_speed = '{:.6f}μs/ {:.6f}MHz'.format(clk, 1/clk) 
    elif clk<1000000:
        comp_speed = '{:.6f}ms/ {:.6f}KHz'.format(clk/1000, 1/(clk/1000)) 
    else:
        comp_speed = '{:.6f}s/ {:.6f}Hz'.format(clk/1000000, 1/(clk/1000000))
    return comp_speed


@app.callback( # multiple output is a new feature since dash==0.39.0
    [Output(component_id = 'tree', component_property = 'elements'),
    Output(component_id = 'assembly_window', component_property = 'children'),
    Output(component_id = 'compile_status', component_property = 'children'),
    Output(component_id = 'compile_status', component_property = 'style'),
    Output(component_id = 'compile_output', component_property = 'children'),
    Output(component_id = 'comp_speed_FPGA', component_property = 'children'),
    Output(component_id = 'comp_speed_CPU', component_property = 'children'),
    Output(component_id = 'tot_scq_size', component_property = 'children'),
    Output(component_id = 'tot_memory', component_property = 'children'),
    Output(component_id = 'resource_usage', component_property = 'figure'),
    ],
    [Input(component_id = 'formula', component_property = 'value'),
    Input(component_id = 'optimization', component_property = 'value'),
    Input(component_id = 'hardware_clk', component_property = 'value'),
    Input(component_id = 'timestamp_length', component_property = 'value'),
    Input(component_id = 'LUT_type', component_property = 'value'),
    Input(component_id = 'resource_type', component_property = 'value'),
    Input(component_id = 'op_exe_time', component_property = 'value'),
    Input(component_id = 'at_exe_time', component_property = 'value'),
    Input(component_id = 'cpu_clk', component_property = 'value'),
    ]
)
def update_element(input, optimization, hw_clk, timestamp_length, LUT_type, resource_type, op_exe_time, at_exe_time, cpu_clk):
    opt_cse = True if 'opt_cse' in optimization else False
    status,logout,stdout,stderr,ast,asm,asm_str,scq_size = compile(input, '', '', True, True, True, True)

    compile_status = "Compile status: "
    if status == 0:
        compile_status += 'ok'
    elif status == 1:
        compile_status += 'failed parsing'
    else:
        compile_status += 'failed type check'

    if (status!=0):
        elements = []
        asm = 'Error'
        compile_output = logout
        # print(stdout)
        style = {'color':'red'}
        comp_speed_FPGA = 'NA'
        comp_speed_CPU = 'NA'
        tot_memory = 'NA'
        resource_fig = data_process.RF
        select_fig = resource_fig.get_LUT_fig()
    else:
        asm = [a for a in asm if not isinstance(a,Program) and not isinstance(a,Specification)]
        asm.reverse()

        asm_str.replace('\t','')
        asm_str.replace('\n','')

        compile_output = stdout

        node = [
            {'data':{'id': str(node), 'num': 0, 'type': str(type(node))[21:-2], 'str':str(node), 'name':node.name,'bpd':node.bpd, 'wpd':node.wpd, 'scq_size':node.scq_size} }
            for node in asm
        ]

        edge = []
        signals = []
        for src in asm:
            for child in src.get_children():
                edge.append({'data':{'source':str(src), 'target':str(child)}})

            if isinstance(src,Signal):
                signals.append(src)

        elements = node + edge
        style = {'color':'green'}
        tot_memory = str(scq_size*int(timestamp_length)/8/1024)+"KB" #KB
        # scq_size_str = str(scq_size) # + "(" + str()+ ")"
        # tmp = pg.tot_time/int(hw_clk)
        tmp = int(hw_clk)
        comp_speed_FPGA = speed_unit_conversion(tmp)
        comp_speed_CPU = speed_unit_conversion(int(at_exe_time)*len(signals)+int(op_exe_time)*scq_size/int(cpu_clk))
        resource_fig = data_process.RF

        resource_fig.config(LUT_type, scq_size, int(timestamp_length))
        select_fig = resource_fig.get_LUT_fig() if resource_type == "LUT" else resource_fig.get_BRAM_fig()

    return elements, asm_str, compile_status, style, compile_output, comp_speed_FPGA, comp_speed_CPU , scq_size, tot_memory, select_fig

if __name__ == '__main__':
    app.run_server(debug=True)






           
