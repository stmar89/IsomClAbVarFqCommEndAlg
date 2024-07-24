fld = ~/IsomClassesAbVarFqComEnd/parallel_End/

all:
	@echo "Removing old input"
	rm ${fld}input.txt || true
	@echo "Prepping new input"
	magma -b ${fld}prep_input.txt
	@echo "Removing old output, joblog and error files"
	rm ${fld}output.txt || true
	rm ${fld}errors.txt || true
	rm ${fld}joblog || true
	@echo "Starting new parallel"
	parallel -j 15 --timeout 3600 --resume --joblog ${fld}joblog -a ${fld}input.txt magma -b cc:={} ${fld}script.txt 
