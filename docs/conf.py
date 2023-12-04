# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))

# -- Project information -----------------------------------------------------

project = 'R2U2'
copyright = '2023, Laboratory for Temporal Logic'
author = 'Laboratory for Temporal Logic'

# The full version, including alpha/beta/rc tags
release = '3.0'


# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    "myst_parser",
    "sphinxcontrib.collections",
    "sphinxcontrib.bibtex",
]

myst_enable_extensions = [
    "attrs_block",

    "amsmath",
    "attrs_inline",
    "colon_fence",
    "deflist",
    "dollarmath",
    "fieldlist",
    "html_admonition",
    "html_image",
    "tasklist",
]

source_suffix = {
    '.rst': 'restructuredtext',
    '.txt': 'markdown',
    '.md': 'markdown',
}

# Use [sphinxcontrib-bibtex](https://pypi.org/project/sphinxcontrib-bibtex/)
bibtex_bibfiles = ['References.bib']

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']


# Use [Sphinx-Collections](https://sphinx-collections.readthedocs.io) to bring
# docs content from subprojects into repo-wide meta-build.
collections_target = "_collections"
collections = {
    "c2po_readme": {
        "driver": "copy_file",
        "source": "../compiler/README.md",
        "target": "c2po_readme.md"
    },
    'c2po_docs': {
        'driver': 'copy_folder',
        'source': '../compiler/docs/',
        # 'target': 'c2po_docs/',
        'ignore': ['*.dat', '.exe'],
    },
    "r2u2_readme": {
        "driver": "copy_file",
        "source": "../monitors/static/README.md",
        "target": "r2u2_readme.md"
    },
    'r2u2_docs': {
        'driver': 'copy_folder',
        'source': '../monitors/static/docs/',
        # 'target': 'r2u2_docs/',
        'ignore': ['*.dat', '.exe'],
    }
}

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = "sphinx_book_theme"
html_title = "R2U2 Documentation"
html_logo = "_static/r2u2-graphic-solo.png"
html_theme_options = {
    "repository_url": "https://gitlab.com/bckempa/r2u2",
    "use_repository_button": True,
    "show_navbar_depth": 1,
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

# -- Options for HTML output -------------------------------------------------

# Place URLs in footnotes instead of in-line parentheticals
epub_show_urls = 'footnote'
