# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line, and also
# from the environment for the first two.
SPHINXOPTS    ?=
SPHINXBUILD   ?= sphinx-build
SOURCEDIR     = .
COLLECTIONDIR = _collections
DOXYGENDIR	  = _doxygen
APIDIR	      = _api
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help clean Makefile

clean: ## Remove all build artifacts
	@echo CLEAN $(BUILDDIR) $(COLLECTIONDIR) $(DOXYGENDIR) $(APIDIR)
	@rm -rf $(BUILDDIR) $(COLLECTIONDIR) $(DOXYGENDIR) $(APIDIR)

# Path rules
$(COLLECTIONDIR):
	mkdir -p $(COLLECTIONDIR)

$(DOXYGENDIR):
	mkdir -p $(DOXYGENDIR)

$(APIDIR):
	mkdir -p $(APIDIR)

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile | $(COLLECTIONDIR) $(DOXYGENDIR) $(APIDIR)
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
