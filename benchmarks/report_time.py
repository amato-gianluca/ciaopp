from matplotlib import pyplot as plt
import pandas as pd
import numpy as np
import sys
import argparse
import os
import re
import csv

def show_graph(df, domains):
    fig, ax = plt.subplots(layout='constrained')
    width = 0.8/len(domains)
    x = np.arange(len(df['program']))
    for i, domain in enumerate(domains):
        ax.bar(x + i*width, df[domain], width=width,  label = domain)
    ax.set_title('Analysis execution time')
    ax.set_ylabel('Time (ms)')
    ax.legend(loc='upper left', ncols=3)
    ax.set_ylim(0, 250)

PROGRAM_STRING = 'Analyzing with aim: '
TIME_STRING = '{analyzed by plai in '

parser = argparse.ArgumentParser(description="Process log files for benchmakrs and report about execution time")
parser.add_argument('-d', '--dir', help='directory of benchmark results')
parser.add_argument('-t', '--table', action='store_true', help='generate table with all results')
parser.add_argument('-g', '--graph', action='store_true', help='generate graph')
args = parser.parse_args()

table = []
domains = []

maindir = args.dir if args.dir else "save"
for program in os.listdir(maindir):
    logfile = os.path.join(maindir, program, 'log')
    with open(logfile, "r") as f:
        table_row = { 'program': program }
        for line in f:
            line = line.strip()
            if line.startswith(PROGRAM_STRING):
                domain = line[line.index(':')+2:-3]
                if domain not in domains:
                    domains.append(domain)
            elif line.startswith(TIME_STRING):
                match = re.search('([0-9]*\\.[0-9]*)', line)
                time = float(match.group(0))
                table_row[domain] = time
    table.append(table_row)

df = pd.DataFrame(table, columns = ['program'] + domains)

if args.table:
    csvwriter = csv.writer(sys.stdout)
    csvwriter.writerow(['program'] + domains)
    for table_row in table:
        line = [table_row['program']]
        for domain in domains:
            line.append(table_row.get(domain, ''))
        csvwriter.writerow(line)

if args.graph:
    show_graph(df, ['share', 'as_sharing_noopt_mgu', 'as_sharing_opt'])
    show_graph(df, ['shfrlin', 'as_shlin_noopt_mgu', 'as_shlin_opt_opt'])
    show_graph(df, ['as_shlin2_noopt_mgu', 'as_shlin2_opt'])
    plt.show()
