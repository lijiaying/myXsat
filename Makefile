SHELL := /bin/bash
CC = clang
# Set dynamic library flag
UNAMES=$(shell uname -s)
ifeq ($(UNAMES),Linux)
	DLIBFLAG=-shared
	PYTHONINC=/usr/include/python2.7/
	PYTHONLIB=/usr/lib/python2.7/
endif
ifeq ($(UNAMES),Darwin)
	DLIBFLAG=-dynamiclib	
	PYTHONINC=
	#/usr/local/Cellar/python/2.7.14/Frameworks/Python.framework/Versions/2.7/include/python2.7/
  PYTHONLIB=
	#/usr/local/Cellar/python/2.7.14/Frameworks/Python.framework/Versions/Current/lib/
endif


XSAT_ := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
OUT_=$(XSAT_)/out
R_SQUARE_=$(OUT_)/R_square
R_ULP_=$(OUT_)/R_ulp
R_VERIFY_=$(OUT_)/R_verify

XSAT_GEN=$(XSAT_)/xsat_gen.py

ifdef IN
   $(shell echo $(IN) > XSAT_IN.txt)
endif


IN:= $(shell cat XSAT_IN.txt)

PYTHON_H:=

define XSAT_echo
	@echo "[XSat] $1 "
endef


all:  compile

solve: compile
	@echo [XSAT] Executing the solver.
	@python xsat.py 

compile:  compile_ulp 

gen:  build/foo.c xsat_gen.py
build/foo.c: $(IN)  XSAT_IN.txt
	@echo "[XSAT] .smt2 -> .c"
	@mkdir -p build
	python2.7 xsat_gen.py $<  > $@

compile_ulp: build/R_ulp/foo.so
build/R_ulp/foo.so: build/foo.c include/R_ulp/xsat.h  $(IN) 
	@echo [XSAT]Compiling the representing function as $@
	@mkdir -p build/R_ulp
	@$(CC) -O3 -fPIC $< $(DLIBFLAG) -o $@  -I include/R_ulp  -I $(PYTHONINC)  -L $(PYTHONLIB) -lpython2.7 -fbracket-depth=3000


test: test_benchmarks.py
	python $<

helloworld: Benchmarks/div3.c.50.smt2
	make IN=$>
	python xsat.py

clean:
	$(XSAT_echo) Cleaning build/ and Results/
	@rm -vf build/foo.c build/foo.symbolTable
	@rm -vfr build/R_square build/R_ulp build/R_verify
	@rm -vf Results/*


.PHONY: copy gen clean compile test


