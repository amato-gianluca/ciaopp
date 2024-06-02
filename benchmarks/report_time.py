import sys
import os
import re
import csv

PROGRAM_STRING = 'Analyzing with aim: '
TIME_STRING = '{analyzed by plai in '

table = []
domains = []

maindir = sys.argv[1] if len(sys.argv) > 1 else "save"
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

csvwriter = csv.writer(sys.stdout)
csvwriter.writerow(['program'] + domains)
for table_row in table:
    line = [table_row['program']]
    for domain in domains:
        line.append(table_row.get(domain, ''))
    csvwriter.writerow(line)
