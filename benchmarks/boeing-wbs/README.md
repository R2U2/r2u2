# Boeing Wheel Brake System Benchmarks

Benchmarks originally adapted from [Formal Design and Safety Analysis of AIR6110 Wheel Brake System](https://doi.org/10.1007/978-3-319-21690-4_36). The artifact can be found at FBK's webpage for [the project](https://es-static.fbk.eu/projects/air6110/index.php?n=Main.Download). The XML files that store the properties are from [More Scalable LTL Model Checking via Discovering Design-Space Dependencies (D3)](https://doi.org/10.1007/978-3-319-89960-2_17) ([Artifact](https://doi.org/10.6084/m9.figshare.5913013.v1))

The script `convert_xml_to_mltl.py` converts each property (which is an LTL property in SMV syntax) to a C2PO and MLTL file. The only temporal operator used is `G`. We add an interval to every `G` operator from the set `{[0,10], [0,100], [0,1000], [10,100], [100,1000]}`. For MLTL files, we also convert all non-Boolean expressions to atomic propositions (e.g., `i + j` becomes `a0`).
