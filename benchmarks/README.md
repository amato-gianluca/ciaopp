This directory contains the benchmarks we use to test the new domains in the `as_*` collection and related scripts.

 In particular:
- `README.md`: this text file.
- `src`: the source code of benchmarks.
- `analysis.sh`: analyzes the programs in `src`, and saves the output in the `results` directory. Each benchmark has its own subdirectory, containing the results of the analysis and a `log` file with execution
times, warnings and error messages.
- `analysis.pl`: old version of `analyze.sh` written in Prolog. Not used anymore.
- `generate_report_time.py`: reads the log files from the directory `results` and generates (in the standard output) a CSV file containing the execution time of all benchmarks. It is possible to specify a different directory for the results of the analysis using the `-d` command line option. The output may be redirected to the file`report_time.csv` for further treatment with the `generate_graph.py` script.
- `generate_report_precision.pl`: reads the results of the analysis from the directory `results` and generates (in the standard output) a CSV file with summary information. The output may be redirected to the file `report_precision.csv` for further treatment with the `generate_graph.py` script. In order to use the program, just gives the following commands from Ciao Prolog from the `benchmarks` directory:
    ```prolog
    :- use_module('generate_report_precision')
    :- run.
    ```
- `generate_graphs.py`: using the files `report_precision.csv` and `report_time.csv`, generates boxplots comparing the different domains.
- `save_yyyymmdd`: results of the analysis taken on the given date and saved for future reference.
- `report_precision.csv`: saved result of the Prolog program `generate_report_precision.pl`.
- `report_time.csv`: saved result of the script `generate_report_time.py`.