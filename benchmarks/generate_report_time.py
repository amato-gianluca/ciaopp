#!/usr/bin/env python3

import argparse
import os
import re
import sys

import pandas as pd


def generate_table(maindir: str):
    PROGRAM_STRING = 'START ANALYSIS'
    EXITCODE_STRING = 'END ANALYSIS'
    TIME_STRING = '{analyzed by plai in '

    table = []
    domains = []

    for program in os.listdir(maindir):
        path = os.path.join(maindir, program)
        if not os.path.isdir(path): continue
        logfile = os.path.join(maindir, program, 'log')
        with open(logfile, "r") as f:
            table_row = { 'program': program }
            for line in f:
                line = line.strip()
                if line.startswith(PROGRAM_STRING):
                    domain = line[line.index(':')+2:]
                    if domain not in domains:
                        domains.append(domain)
                elif line.startswith(TIME_STRING):
                    match = re.search('([0-9]*\\.[0-9]*)', line)
                    if not match:
                        sys.exit("time expected after 'analyzer by plain in' string")
                    time = float(match.group(0))
                    table_row[domain] = str(time)
                elif line.startswith(EXITCODE_STRING):
                    exitcode = line[line.index(':')+2:]
                    if exitcode == "124":
                        table_row[domain] = 'TIMEOUT'
                    elif exitcode == "1":
                        table_row[domain] = 'OOM'
                    elif exitcode != "0":
                        raise ValueError('Unexpected exit code: ' + exitcode)
        table.append(table_row)
    df = pd.DataFrame(table, columns = ['program'] + domains).set_index('program').sort_index()
    df.to_csv(sys.stdout)

def main():
    parser = argparse.ArgumentParser(description="Process log and generate a report on execution time.")
    parser.add_argument('-d', '--dir', default='results', help='directory where benchmark results are stored')
    args = parser.parse_args()
    generate_table(args.dir)

if __name__ == "__main__":
    main()
