USER_DIR := UsersGuide
USER_NAME := R2U2_Users_Guide

DEV_DIR := DevelopersGuide
DEV_NAME := R2U2_Developers_Guide

API_DIR := APIGuide
API_NAME := R2U2_API_Guide

all: user dev api

user:
	cd $(USER_DIR) && latexmk -jobname=$(USER_NAME) -pdf main.tex
	cd $(USER_DIR) && latexmk -jobname=$(USER_NAME) -c

dev:
	cd $(DEV_DIR) && latexmk -jobname=$(DEV_NAME) -pdf main.tex
	cd $(DEV_DIR) && latexmk -jobname=$(DEV_NAME) -c

api:
	$(MAKE) -C ../R2U2_C doc
	$(MAKE) -C ../R2U2_C/doc/latex
	cp ../R2U2_C/doc/latex/refman.pdf $(API_DIR)/$(API_NAME).pdf

clean:
	cd $(USER_DIR) && latexmk -jobname=$(USER_NAME) -c
	rm $(USER_DIR)/$(USER_NAME).pdf
	cd $(DEV_DIR) && latexmk -jobname=$(DEV_NAME) -c
	rm $(DEV_DIR)/$(DEV_NAME).pdf
	$(MAKE) -C ../R2U2_C/doc/latex clean
	rm $(API_DIR)/$(API_NAME).pdf
