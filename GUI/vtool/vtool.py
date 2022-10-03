#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# pip install dash-cytoscape==0.1.1
# 
import json
import dash
import dash_core_components as dcc
import dash_html_components as html
import dash_cytoscape as cyto
from dash.dependencies import Input, Output
from textwrap import dedent as d

# import MLTL compiler
from MLTL_Compiler import *

cyto.load_extra_layouts()

external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']
app = dash.Dash(__name__, external_stylesheets=external_stylesheets)
server = app.server

app.title = "MLTL Compiler"
default_stylesheet = [
    {
        'selector': '[type = "ATOM"]',
        'style': {
            'background-color': '#ff9900',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "BOOL"]',
        'style': {
            'background-color': '#BFD7B5',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "NEG"]',
        'style': {
            'background-color': '#66ff99',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "GLOBAL"]',
        'style': {
            'background-color': '#6699ff',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "AND"]',
        'style': {
            'background-color': '#ff6666',
            'label': 'data(name)'
        }
    },
    {
        'selector': '[type = "UNTIL"]',
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

app.layout = html.Div([
################title
    html.Div(
        [html.H1('R2U2 MLTL Compiler')],
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
                            **MLTL Formula**                         
                            """)),
                    dcc.Input(id='formula', value='a0 U[5] a1', type='text'),
                    html.Pre(id='compile_status', style = {'color': 'green'}),
                    dcc.Markdown(d("""   
                            **Prediction Horizon Hp**  
                            """)),
                    dcc.Input(id='pred_length', value='0', type='text')
                    ],
                    style={'height': '300px'}
                ),

            html.Div(
                className = 'five columns',
                children = [
                    cyto.Cytoscape(
                        id='tree',
                        # layout={'name': 'circle'},
                        layout={'name': 'klay','klay': {'direction': 'DOWN'}},
                        stylesheet=default_stylesheet,
                        style={'width': '100%', 'height': '450px'},
                        elements=[]
                    ),
                ]
            ),

            html.Div(
                className = 'four columns',
                children = [
                    dcc.Tabs(
                        id='tabs', 
                        children=[            
                            dcc.Tab(
                                label='Mouseover Data', 
                                children=[
                                    html.Div(
                                        style=styles['tab'], 
                                        children=[
                                            html.P(id='status',children=['Init']),
                                            # html.P('Node Data JSON:'),
                                            html.Pre(
                                                id='mouseover-node-data-json-output',
                                                style=styles['json-output']
                                            ),
                                            html.P('Edge Data JSON:'),
                                            html.Pre(
                                                id='mouseover-edge-data-json-output',
                                                style=styles['json-output']
                                            )
                                        ]
                                    )
                                ]
                            ),
                            dcc.Tab(
                                label='Assembly Output', 
                                children=[
                                    html.Div(
                                        style=styles['tab'], 
                                        children=[
                                            html.P('Assembly:'),
                                            html.Pre(
                                                id='assembly_window',
                                                style=styles['json-output'],
                                            ),
                                        ]
                                    )
                                ]
                            ),     
                            
                        ]
                    )
                ]
            )
        ],  
    ),
])

@app.callback(Output('mouseover-edge-data-json-output', 'children'),
              [Input('tree', 'mouseoverEdgeData')])
def displayMouseoverEdgeData(data):
    return json.dumps(data, indent=2)

@app.callback(
    Output('mouseover-node-data-json-output', 'children'),
    [Input('tree', 'mouseoverNodeData')])
def displayMouseoverNodeTitle(data):
    if (data==None or 'bpd' not in data):
        return html.P('None')
    return html.P(
        'Name:'+str(data['name'])+'\n'
        +'bpd:'+str(data['bpd'])+'\n'
        +'wpd:'+str(data['wpd'])+'\n'
        +'SCQ size:'+str(data['scq_size'])+'\n'
        )

@app.callback(Output('status', 'children'),
              [Input('tree', 'mouseoverNodeData')])
def displayMouseoverNodeData(data):
    if (data==None or 'num' not in data):
        return html.P('Node: Unselected')
    return html.P('Node: '+str(data['num']))


@app.callback( # multiple output is a new feature since dash==0.39.0
    [Output(component_id = 'tree', component_property = 'elements'),
    Output(component_id = 'assembly_window', component_property = 'children'),
    Output(component_id = 'compile_status', component_property = 'children'),
    Output(component_id = 'compile_status', component_property = 'style')
    ],
    [Input(component_id = 'formula', component_property = 'value'),
    Input(component_id = 'pred_length', component_property = 'value')]
)
def update_element(formula, pred_length):
    pg = Postgraph(MLTL=formula,Hp=int(pred_length),optimize_cse=True)
    compile_status = "Compile status: "+ pg.status.upper()
    if (pg.status!='pass'):
        elements = []
        assembly_window = 'Error'
        style = {'color':'red'}
    else:
        node = [
            {'data':{'id': str(node), 'num': num, 'type': node.type, 'name':node.name,'bpd':node.bpd, 'wpd':node.wpd, 'scq_size':node.scq_size} }
            for num , node in enumerate(pg.valid_node_set)
        ]

        edge = []
        for src in pg.valid_node_set:
            if (src.left):
                edge.append({'data':{'source':str(src), 'target':str(src.left)}})
            
            if (src.right):
                edge.append({'data':{'source':str(src), 'target':str(src.right)}})

        elements = node + edge
        assembly_window = pg.asm
        style = {'color':'blue'}

    return elements, assembly_window, compile_status, style





if __name__ == '__main__':
    app.run_server(debug=True)






