fld = ~/IsomClassesAbVarFqComEnd/parallel_storing/
file_input = ${fld}input.txt
file_input_special = ${fld}input_special.txt
fld_out = ${fld}output/
file_err = ${fld}/errors.txt
jobs = 15
timeout = 7200

all: clean_old_parallel parallel

prep_input:
	@echo "Removing old input"
	rm ${file_input} || true
	@echo "Prepping new input"
	magma -b ${fld}prep_input.txt

clean_old_parallel:
	@echo "Removing old joblog"
	git rm ${fld}joblog || true
	@echo "Removing old error file"
	git rm ${file_err} || true

parallel:
	@echo "Starting the parallel"
	parallel -j ${jobs} --timeout ${timeout} --resume --joblog ${fld}joblog -a ${file_input} magma -b cc:={} fld_out:=${fld_out} file_err:=${file_err} ${fld}script.txt 
	@echo "parallel is done! Congrats!"
	

parallel_special:
	@echo "Removing old joblog"
	git rm ${fld}joblog_special || true
	@echo "Starting the parallel on special input without timeout"
	parallel -j ${jobs} --resume --joblog ${fld}joblog_special -a ${file_input_special} magma -b cc:={} fld_out:=${fld_out} file_err:=${file_err} ${fld}script.txt 
	@echo "parallel is done! Congrats!"
	

