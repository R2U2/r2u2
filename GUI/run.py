#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# pip install dash-cytoscape==0.1.1
# 
# type: ignore
import dash
from dash import html, dcc
import dash_cytoscape as cyto
import dash_bootstrap_components as dbc
from dash.dependencies import Input, Output, State
from textwrap import dedent as d

import plotly.graph_objects as go
from c2po.c2po import *
from c2po.ast import *
import data_process

cpu_latency_table = default_cpu_latency_table.copy()
fpga_latency_table = default_fpga_latency_table.copy()

cyto.load_extra_layouts()

app = dash.Dash(__name__,external_stylesheets=[dbc.themes.BOOTSTRAP])
server = app.server

app.title = "R2U2 Resource Estimator"

default_stylesheet = [ 
    {
        "selector": "[type = \""+cls.__name__+"\"]",
        "style": {
            "background-color": "#cc00cc",
            "label": "data(name)"
        }
    }
    for cls in instruction_list if issubclass(cls, TemporalOperator)
] + [
    {
        "selector": "[type = \""+cls.__name__+"\"]",
        "style": {
            "background-color": "#66ff99",
            "label": "data(name)"
        }
    }
    for cls in instruction_list if issubclass(cls, LogicalOperator)
] + [
    {
        "selector": "[type = \""+cls.__name__+"\"]",
        "style": {
            "background-color": "#BFD7B5",
            "label": "data(name)"
        }
    }
    for cls in instruction_list if issubclass(cls, BZInstruction)
] + [
    {
        "selector": "edge",
        "style": {
            "curve-style": "bezier",
            "target-arrow-color": "grey",
            "target-arrow-shape": "vee",
            "line-color": "grey"
        }
    }
]

styles = {
    "json-output": {
        "overflow-y": "scroll",
        "height": "calc(50% - 25px)",
        "border": "thin lightgrey solid"
    },
    "tab": {"height": "calc(98vh - 115px)"},
}

app.layout = html.Div(

    children = [
################title
    html.Div(
        [html.H1("R2U2 Resource Estimator")],
        className = "row",
        style = {"textAlign":"center"}
        ),

############### left view
    html.Div(
        className = "row",
        children= [
            html.Div(
                className = "two columns",
                children = [
                    # dcc.Markdown(d("""
                    #         ###### C2PO Input
                    #         """)),
                    # dcc.Input(id="formula", value="a0 U[5] a1; a1&a3;", type="text"),
                    # dcc.Markdown(d("**C2PO Input**")),
                    html.Div("C2PO Input"),
                    dcc.Textarea(
                        id="formula",
                        value="INPUT\n  a0,a1,a2: bool;\n  b0,b1,b2: bool;\n\nDEFINE\n  c = a1 || a2;\n\nFTSPEC\n  s0: a0;\n  s1: c;\n  s2: b0 U[0,5] b1;\n  s3: G[1,3] b2;\n  s4: s2 && s3;" ,
                        style={"width": "100%", "height": "350px", "font-family": "monospace"},
                    ),
                    # html.Div("Int type"),
                    dcc.Dropdown(
                        id = "int-type",
                        options=[
                            {"label": "uint8_t", "value": "uint8_t"},
                            {"label": "uint16_t", "value": "uint16_t"},
                            {"label": "uint32_t", "value": "uint32_t"},
                            {"label": "uint64_t", "value": "uint64_t"},
                            {"label": "int8_t", "value": "int8_t"},
                            {"label": "int16_t", "value": "int16_t"},
                            {"label": "int32_t", "value": "int32_t"},
                            {"label": "int64_t", "value": "int64_t"},
                        ],
                        value="uint8_t",
                        clearable=False
                    ),
                    dcc.Dropdown(
                        id = "float-type",
                        options=[
                            {"label": "float", "value": "float"},
                            {"label": "double", "value": "double"}
                        ],
                        value="float",
                        clearable=False
                    ),
                    dcc.Checklist(
                        id = "compiler-opt",
                        style = {"font-size": "70%"},
                        options=[
                            {"label": "Common Subexpression Elimination", "value": "cse"},
                            {"label": "Booleanizer", "value": "bz"},
                            {"label": "Extended Operators", "value": "extops"}
                        ],
                        value=["cse","bz","extops"]
                    ),
                    dbc.Button(
                        "Compile", id="run-compile", className="ms-auto", n_clicks=0
                    ),
                    html.Pre(id="compile_status", style = {"color": "blue"}),

                    html.Div(
                        # className = "one column",
                        style = {"height": "350px"},
                        children=[
                            # dcc.Markdown(d("""
                            #         ###### C2PO Log
                            #         """)),
                            html.Div("C2PO Log"),
                            html.Pre(
                                id="compile_output",
                                style=styles["json-output"],
                            )
                        ]
                    ),
                    ],
                    
                ),

                html.Div(
                    className = "two columns",
                    children = [

                    # dcc.Markdown(d("#### Software Configuration")),
                    html.Div("Software Configuration"),
                    html.Div(
                            style={"backgroundColor": "#A2F0E4"},
                            children = [
                                # dcc.Markdown(d("#### Software Configuration")),
                                dcc.Markdown(d("**Clock Frequency (GHz)**")),
                                dcc.Input(style={"backgroundColor": "#A2F0E4"}, id="cpu_clk", value="10", type="text", size="5"),
                                # Command exection time for each operator
                                dcc.Markdown(d("**CPU Operator Latencies**")),
                                dbc.Button("Edit", id="cpu-open", n_clicks=0),
                                dbc.Modal(
                                    # style = {"width": "500px"},
                                    children = [
                                        dbc.ModalHeader(dbc.ModalTitle(
                                            children = [ dcc.Markdown(d("**CPU Operator Latencies**")), ]
                                        )),
                                        dbc.ModalBody(
                                            [html.Div(
                                                style={"backgroundColor": "#A2F0E4"},
                                                children = [
                                                    html.Div(name, style={"width": "40%", "display": "inline-block"}), 
                                                    dcc.Input(style={"backgroundColor": "#A2F0E4", "display": "inline-block"}, id=name+"cpu-latency", value=val, size="5")
                                                ]) for (name,val) in default_cpu_latency_table.items()]
                                        ),
                                        dbc.ModalFooter(
                                            dbc.Button(
                                                "Update", id="cpu-close", className="ms-auto", n_clicks=0
                                            )
                                        ),
                                    ],
                                    id="cpu-modal",
                                    is_open=False,
                                ),
                                # dcc.Markdown(d("**TL Clock Cycles**")),
                                # dcc.Input(style={"backgroundColor": "#A2F0E4"}, id="op_exe_time", value="10", type="text", size="5"),
                                # # Processing time for each atomic checker
                                # dcc.Markdown(d("**BZ Clock Cycles**")),
                                # dcc.Input(style={"backgroundColor": "#A2F0E4"}, id="at_exe_time", value="10", type="text", size="5"),
                                dcc.Markdown(d("**Worst-case Exec. Time**")),
                                html.Div(id="comp_speed_CPU",),
                                dcc.Markdown(d("**Est. SCQ Memory**")),
                                html.Div(id="tot_memory",),
                            ]
                        ),
                    ]
                ),



                html.Div(
                className = "two columns",
                children = [
                        # dcc.Markdown(d("#### Hardware Configuration")),
                    # dcc.Markdown(d("**Hardware Configuration**")),
                    html.Div("Hardware Configuration"),
                    html.Div(
                        style={"backgroundColor": "#F7FAC0"},
                        children  = [
                        # dcc.Markdown(d("---\n#### Hardware Configuration")),
                        dcc.Markdown(d("**Clock Frequency (MHz)**")),
                        dcc.Input(style={"backgroundColor": "#F7FAC0"},id="hardware_clk", value="100", type="text", size="5"),
                        dcc.Markdown(d("**LUT Type Select**")),
                        dcc.Dropdown(
                            id = "LUT_type",
                            style={"backgroundColor": "#F7FAC0", "width": "80%"},
                            options=[
                                {"label": "LUT-3", "value": "3"},
                                {"label": "LUT-4", "value": "4"},
                                {"label": "LUT-6", "value": "6"},
                            ],
                            value="3",
                            clearable=False
                        ),
                        dcc.Markdown(d("**Resource to Observe**")),
                        dcc.Dropdown(
                            id = "resource_type",
                            style={"width": "80%", "backgroundColor": "#F7FAC0"},
                            options=[
                                {"label": "LUT", "value": "LUT"},
                                {"label": "BRAM", "value": "BRAM"},
                            ],
                            value="LUT",
                            clearable=False
                        ),

                        dcc.Markdown(d("**Timestamp Length (Bits)**")),
                        dcc.Input(style={"backgroundColor": "#F7FAC0"},id="timestamp_length", value="32", type="text", size="5"),

                        dcc.Markdown(d("**Comparators per Node**")),
                        dcc.Input(style={"backgroundColor": "#F7FAC0"},id="comps", value="33", type="text", size="5"),

                        dcc.Markdown(d("**Adders per Node**")),
                        dcc.Input(style={"backgroundColor": "#F7FAC0"},id="adds", value="32", type="text", size="5"),

                        dcc.Markdown(d("**FPGA Operator Latencies**")),
                        dbc.Button("Edit", id="fpga-open", n_clicks=0),
                        dbc.Modal(
                            # style = {"width": "500px"},
                            children = [
                                dbc.ModalHeader(dbc.ModalTitle(
                                    children = [ dcc.Markdown(d("**FPGA Operator Latencies**")), ]
                                )),
                                dbc.ModalBody(
                                    [html.Div(
                                        style={"backgroundColor": "#F7FAC0"},
                                        children = [
                                            html.Div(name, style={"width": "40%", "display": "inline-block"}), 
                                            dcc.Input(style={"backgroundColor": "#F7FAC0", "display": "inline-block"}, id=name+"fpga-latency-init", value=init, size="5"),
                                            dcc.Input(style={"backgroundColor": "#F7FAC0", "display": "inline-block"}, id=name+"fpga-latency-eval", value=eval, size="5")
                                        ]) for (name,(init,eval)) in default_fpga_latency_table.items()]
                                ),
                                dbc.ModalFooter(
                                    dbc.Button(
                                        "Update", id="fpga-close", className="ms-auto", n_clicks=0
                                    )
                                ),
                            ],
                            id="fpga-modal",
                            is_open=False,
                        ),
                        # dcc.Slider(
                        #     id="timestamp_length",
                        #     min=0,
                        #     max=64,
                        #     step=1,
                        #     value=32,
                        #     marks=None
                        # ),
                        # html.Div(style="width:500px;height:100px;border:1px solid #000;"),
                        # html.Div(id="slider-output-container-ts"),
                        # dcc.Input(id="timestamp_length", value="32", type="text"),
                        html.Div(
                        # style={"backgroundColor": "#A2F0E4"},
                        children = [
                            # dcc.Markdown(d("---\n### Results for Timing and Resource")),
                            dcc.Markdown(d("**Worst-case Exec. Time**")),
                            html.Div(id="comp_speed_FPGA",),
                            dcc.Markdown(d("**Total SCQ Memory Slots**")),
                            html.Div(id="tot_scq_size",),
                        ]
                    ),


                        ],
                    ),
                ],
                # style={"width": "15%"}
            ),

            html.Div(
                className = "three columns",
                children = [
                    cyto.Cytoscape(
                        id="tree",
                        # layout={"name": "circle"},
                        layout={"name": "klay","klay": {"direction": "DOWN"}},#, "borderSpacing": 0, "spacing": 3, "compactComponents": False}},
                        stylesheet=default_stylesheet,
                        style={"width": "100%", "height": "350px"},
                        elements=[]
                    ),
                    # dcc.Markdown(d("**Resource to Observe**")),
                    # dcc.Dropdown(
                    #     id = "resource_type",
                    #     style={"width": "80%"},
                    #     options=[
                    #         {"label": "LUT", "value": "LUT"},
                    #         {"label": "BRAM", "value": "BRAM"},
                    #     ],
                    #     value="LUT",
                    #     clearable=False
                    # ),  
                    dcc.Graph(
                        id="resource_usage",
                        figure = go.Figure(),
                        style={"width": "100%"},
                        config={"frameMargins": 0}
                    )
                ],
                # style={"width": "30%"}
            ),


            html.Div(
                className = "two columns",
                # style = {"height": "500px"},
                children = [
                    html.Div(
                        # className = "one column",
                        style = {"height": "300px"},
                        children=[
                        # dcc.Markdown(d("#### Mouseover Data")),
                        html.Div("Mouseover Data"),
                        html.Pre(
                            id="mouseover-node-data-json-output",
                            # style=styles["json-output"]
                        )
                        ]
                    ),
                    html.Div(
                        # className = "one column",
                        style = {"height": "750px"},
                        children=[
                            # dcc.Markdown(d("#### Assembly")),
                            html.Div("Assembly"),
                            html.Pre(
                                id="assembly_window",
                                style=styles["json-output"],
                            )
                        ]
                    ),
                
                ],

            )
        ],  
    ),
])

# @app.callback(
#     Output("slider-output-container-ts", "children"),
#     [Input("timestamp_length", "value")])
# def update_output(value):
#     return "You have selected "{}" bit".format(value)

# @app.callback(Output("mouseover-edge-data-json-output", "children"),
#               [Input("tree", "mouseoverEdgeData")])
# def displayMouseoverEdgeData(data):
#     return json.dumps(data, indent=2)

@app.callback(
    Output("cpu-modal", "is_open"),
    [Input("cpu-open", "n_clicks"), 
     Input("cpu-close", "n_clicks")],
    [State("cpu-modal", "is_open")]
)
def toggle_cpu_modal(open, close, is_open):
    if open or close:
        return not is_open
    return is_open

@app.callback(
    Output("fpga-modal", "is_open"),
    [Input("fpga-open", "n_clicks"), 
     Input("fpga-close", "n_clicks")],
    [State("fpga-modal", "is_open")]
)
def toggle_fpga_modal(open, close, is_open):
    if open or close:
        return not is_open
    return is_open


# @app.callback(
#     Output("slider-output-container-ts", "children"),
#     [Input("timestamp_length", "value")])
# def update_output(value):
#     return "You have selected "{}" bit".format(value)


@app.callback(
    Output("mouseover-node-data-json-output", "children"),
    [Input("tree", "mouseoverNodeData")])
def displayMouseoverNodeTitle(data):
    if (data==None or "bpd" not in data):
        return html.Pre("None Selected")
    return html.Pre(
        "Expression: "+str(data["str"])+"\n"
        +"Node: "+str(data["name"])+"\n"
        +"BPD: "+str(data["bpd"])+"\n"
        +"WPD: "+str(data["wpd"])+"\n"
        +"SCQ size: "+str(data["scq_size"])+"\n"
        )


# @app.callback(Output("selected-node", "children"),
#               [Input("tree", "mouseoverNodeData")])
# def displayMouseoverNodeData(data):
#     if (data==None or "num" not in data):
#         return html.P("Selected Node: NA")
#     return html.P("Selected Node: "+str(data["str"]))


def speed_unit_conversion(clk):
    if clk <= 0:
        comp_speed = "Error: Clock speed must be > 0!"
    elif clk<1000:
        comp_speed = "{:.5f}μs/ {:.5f}MHz".format(clk, 1/clk) 
    elif clk<1000000:
        comp_speed = "{:.5f}ms/ {:.5f}KHz".format(clk/1000, 1/(clk/1000)) 
    else:
        comp_speed = "{:.5f}s/ {:.5f}Hz".format(clk/1000000, 1/(clk/1000000))
    return comp_speed


@app.callback( # multiple output is a new feature since dash==0.39.0
    [Output(component_id = "tree", component_property = "elements"),
    Output(component_id = "assembly_window", component_property = "children"),
    Output(component_id = "compile_status", component_property = "children"),
    Output(component_id = "compile_status", component_property = "style"),
    Output(component_id = "compile_output", component_property = "children"),
    Output(component_id = "comp_speed_FPGA", component_property = "children"),
    Output(component_id = "comp_speed_CPU", component_property = "children"),
    Output(component_id = "tot_scq_size", component_property = "children"),
    Output(component_id = "tot_memory", component_property = "children"),
    Output(component_id = "resource_usage", component_property = "figure"),
    ],
    [Input("run-compile", "n_clicks"),
    Input(component_id = "hardware_clk", component_property = "value"),
    Input(component_id = "timestamp_length", component_property = "value"),
    Input(component_id = "comps", component_property = "value"),
    Input(component_id = "adds", component_property = "value"),
    Input(component_id = "LUT_type", component_property = "value"),
    Input(component_id = "resource_type", component_property = "value"),
    Input(component_id = "cpu_clk", component_property = "value"),
    Input(component_id = "cpu-close", component_property = "n_clicks"),
    Input(component_id = "fpga-close", component_property = "n_clicks")
    ],
    [State(component_id = "formula", component_property = "value"),
     State(component_id = "compiler-opt", component_property = "value"),
     State(component_id = "int-type", component_property = "value"),
     State(component_id = "float-type", component_property = "value"),] +
    [State(component_id=name+"cpu-latency", component_property="value") for name in default_cpu_latency_table.keys()] +
    [State(component_id=name+"fpga-latency-init", component_property="value") for name in default_fpga_latency_table.keys()] +
    [State(component_id=name+"fpga-latency-eval", component_property="value") for name in default_fpga_latency_table.keys()]
)
def update_element(run_compile, hw_clk, timestamp_length, comps, adds, LUT_type, resource_type, cpu_clk, cpu_close, fpga_close, input, options, int_type, float_type, *argv):
    cse = True if "cse" in options else False
    bz = True if "bz" in options else False
    extops = True if "extops" in options else False

    int_width = 8
    int_is_signed = False
    if int_type == "uint8_t":
        int_width = 8
        int_is_signed = False
    elif int_type == "uint16_t":
        int_width = 16
        int_is_signed = False
    elif int_type == "uint32_t":
        int_width = 32
        int_is_signed = False
    elif int_type == "uint64_t":
        int_width = 64
        int_is_signed = False
    elif int_type == "int8_t":
        int_width = 8
        int_is_signed = True
    elif int_type == "int16_t":
        int_width = 16
        int_is_signed = True
    elif int_type == "int32_t":
        int_width = 32
        int_is_signed = True
    elif int_type == "int64_t":
        int_width = 64
        int_is_signed = True

    float_width = 32
    if float_type == "float":
        float_width = 32
    elif float_type == "double":
        float_width = 64

    status,logout,stderr,asm_str,program = compile(input, "", int_width=int_width, int_signed=int_is_signed, float_width=float_width, cse=cse, bz=bz, extops=extops)

    compile_output = stderr+logout

    compile_status = "Compile status: "
    if status > 0:
        compile_status += "fail"
        elements = []
        asm = "Error"
        style = {"color":"red"}
        fpga_wcet_str = "NA"
        cpu_wcet_str = "NA"
        total_memory = "NA"
        resource_fig = data_process.RF
        select_fig = resource_fig.get_LUT_fig(0,0)
    else:
        compile_status += "ok"

        asm = [a for a in program.assembly if not isinstance(a, Program) and not isinstance(a, Specification) and not isinstance(a, SpecificationSet)]

        node = [
            {"data":{"id": str(node), "num": 0, "type": type(node).__name__, "str":str(node), "name":node.name,"bpd":node.bpd, "wpd":node.wpd, "scq_size":node.scq_size} }
            for node in asm
        ]

        edge = []
        for src in asm:
            for child in src.get_children():
                edge.append({"data":{"source":str(src), "target":str(child)}})

        elements = node + edge
        style = {"color": "green"}
        
        total_memory = str((program.total_scq_size*int(timestamp_length))/8/1024)+"KB" #KB

        cpu_vals = argv[0:len(default_cpu_latency_table)-1]
        fpga_vals_list = argv[len(default_cpu_latency_table):]

        fpga_vals = []
        for i in range(0,int(len(fpga_vals_list)/2)):
            fpga_vals.append((fpga_vals_list[i*2],fpga_vals_list[i*2+1]))

        cpu_latency_table.update(dict(zip(list(default_cpu_latency_table), [int(val) for val in cpu_vals])))
        fpga_latency_table.update(dict(zip(list(default_fpga_latency_table), [(float(init),float(eval)) for (init,eval) in fpga_vals])))

        compute_cpu_wcet(program, cpu_latency_table, int(cpu_clk))
        cpu_wcet_str = speed_unit_conversion(program.cpu_wcet)

        # scq_size_str = str(scq_size) # + "(" + str()+ ")"
        # tmp = pg.tot_time/int(hw_clk)
        compute_fpga_wcet(program, fpga_latency_table, int(hw_clk))
        fpga_wcet_str = speed_unit_conversion(program.fpga_wcet)
        resource_fig = data_process.RF

        resource_fig.config(LUT_type, program.total_scq_size, int(timestamp_length))
        select_fig = resource_fig.get_LUT_fig(comps, adds) if resource_type == "LUT" else resource_fig.get_BRAM_fig()

    return elements, asm_str, compile_status, style, compile_output, fpga_wcet_str, cpu_wcet_str, program.total_scq_size, total_memory, select_fig

if __name__ == "__main__":
    app.run_server(debug=True)






           
