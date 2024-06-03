#!/usr/bin/env python3

from matplotlib import pyplot as plt
import pandas as pd
import numpy as np
import sys
import argparse
import os
import re

def domain_name(domain):
    if domain == 'share' or domain.startswith('as_sharing_'):
        return 'Sharing'
    elif domain == 'shfrlin' or domain.startswith('as_shlin_'):
        return 'Sharing * Lin'
    elif domain.startswith('as_shlin2_'):
        return 'ShLin²'
    else:
        raise ValueError('Analysis not supported')

def domain_options(domain):
    if domain == 'share' or domain == 'shfrlin':
        return 'builtin'
    elif domain.endswith('_noopt_mgu'):
        return 'no optimal\nno match'
    elif domain.endswith('_noopt'):
        return 'no optimal\nmatch'
    elif domain.endswith('_opt'):
        return 'optimal\nmatch'
    else:
        raise ValueError('Analysis not supported')

def show_graph(df, domains):
    _, ax = plt.subplots(layout='constrained')
    width = 0.8/len(domains)
    x = np.arange(len(df['program']))
    for i, domain in enumerate(domains):
        ax.bar(x + i*width, df[domain], width=width, label = domain)
    ax.set_title('Analysis execution time')
    ax.set_xlabel(domains)
    ax.set_ylabel('Time (ms)')
    ax.legend(loc='upper left', ncols=3)
    ax.set_ylim(0, 250)

def show_hist(df, domains):
    _, axs = plt.subplots(ncols=len(domains))
    bins=10
    for i, dom in enumerate(domains):
        logbins = np.logspace(np.log10(np.min(df[dom])),np.log10(np.max(df[dom])),bins+1)
        axs[i].hist(df[dom], bins=logbins)
        axs[i].set_xscale('log')
        axs[i].set_title(dom)

def show_boxplot(df, domains, outliers):
    fig, ax = plt.subplots()
    labels = [domain_options(dom) for dom in domains]
    ax.boxplot(df[domains], showfliers=outliers, labels=labels)
    ax.set_title('Analysis execution time with domain ' + domain_name(domains[0]))
    ax.set_ylabel('Time (ms)')
    return fig

def main():
    PROGRAM_STRING = 'Analyzing with aim: '
    TIME_STRING = '{analyzed by plai in '

    parser = argparse.ArgumentParser(description="Process log files for benchmakrs and report about execution time")
    parser.add_argument('-d', '--dir', help='directory where benchmark results are stored')
    parser.add_argument('-t', '--table', action='store_true', help='generate table with all results on stdout')
    parser.add_argument('-b', '--boxplot', action='store_true', help='generate boxplots')
    parser.add_argument('-o', '--output', action='store', default='', help='base filename for PDF files')
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
        df.to_csv(sys.stdout, index=False)

    if args.boxplot:
        df_selection = df.dropna()
        #df_selection= df[df.apply(lambda row: all(float(column) <= 100 for column in row[1:]), axis=1)]
        fig1 = show_boxplot(df_selection, ['share', 'as_sharing_noopt_mgu', 'as_sharing_noopt', 'as_sharing_opt'], False)
        fig2 = show_boxplot(df_selection, ['shfrlin', 'as_shlin_noopt_mgu', 'as_shlin_noopt', 'as_shlin_opt_opt'], False)
        fig3 = show_boxplot(df_selection, ['as_shlin2_noopt_mgu', 'as_shlin2_noopt', 'as_shlin2_opt'], False)
        if args.output == '':
            plt.show()
        else:
            filename = args.output
            fig1.savefig(filename + '1.pdf')
            fig2.savefig(filename + '2.pdf')
            fig3.savefig(filename + '3.pdf')

    #show_graph(df, ['share', 'as_sharing_noopt_mgu', 'as_sharing_opt'])
    #show_graph(df, ['shfrlin', 'as_shlin_noopt_mgu', 'as_shlin_opt_opt'])
    #show_graph(df, ['as_shlin2_noopt_mgu', 'as_shlin2_opt'])
    #show_hist(df, ['share', 'as_sharing_noopt_mgu', 'as_sharing_noopt', 'as_sharing_opt'])

if __name__ == "__main__":
    main()
