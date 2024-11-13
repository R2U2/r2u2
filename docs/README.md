# R2U2 Documentation

Combines high-level documentation with sub-project specific resources to
produce a unified documentation site for use and development of R2U2.

## Building the Docs

1. Install required python modules `pip install -r requirements.txt`
2. Run `make` from the `r2u2/docs` directory to get a list of output formats
3. Select a format and build (e.g., `make html`)
4. Open resulting artifact (e.g., `_build/html/index.html`)

## Writing Docs

The Myst plugin is used parse markdown source files. See the [MyST documentation](https://myst-parser.readthedocs.io/en/latest/syntax/typography.html) for examples of the available syntax.

Files from the individual subproject trees are copied in during doc builds by the collections plugin which is configured in the `conf.py` file.
General document source can live here. Some directories are configured to automatically add all .md files to the build, while others will need to be manually added to the tables of contents (toctree) in `index.md`
