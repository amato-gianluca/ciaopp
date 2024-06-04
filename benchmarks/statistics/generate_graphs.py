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
        return 'ShLin'
    elif domain.startswith('as_shlin2_'):
        return 'ShLin²'
    else:
        raise ValueError('Analysis not supported')

def domain_option(domain):
    if domain == 'share' or domain == 'shfrlin':
        return 'builtin'
    elif domain.endswith('_noopt_mgu'):
        return 'base'
    elif domain.endswith('_noopt'):
        return 'match'
    elif domain.endswith('_opt'):
        return 'optimal'
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

def show_boxplot(df, domains, property):
    fig, ax = plt.subplots()
    if property == 'time':
        titlename = 'analysis time'
        ylabel = 'Time (ms)'
        outliers = False
    else:
        if property == 'mshare':
            titlename = 'number of sharing groups'
        elif property == 'linear':
            titlename = 'number of linear variables'
        else:
            titlename = 'number of ground variables'
        ylabel = 'Ratio w.r.t. builtin Sharing domain (%)'
        outliers = True

    domain_names = [domain_name(dom) for dom in domains]
    domain_options = [domain_option(dom) for dom in domains]
    if all([domain == domain_names[0] for domain in domain_names]):
        ax.boxplot(df[domains], showfliers=outliers, labels=domain_options)
        ax.set_title(f'{titlename.capitalize()} with domain ' + domain_names[0])
    else:
        ax.boxplot(df[domains], showfliers=outliers, labels=domain_names)
        ax.set_title(f'Comparing {titlename} of different domains\n(best options for each domain)')
    ax.set_ylabel(ylabel)
    return fig

def main():
    parser = argparse.ArgumentParser(description="Generate graphs from CSV files")
    parser.add_argument('-p', '--property', action='store', default='time', help='choose property to graph')
    parser.add_argument('-o', '--output', action='store', default='', help='base filename for PDF files')
    args = parser.parse_args()

    if args.property != 'time':
        df = pd.read_csv('report_precision.csv', index_col=['property', 'program']).dropna()
        if args.property == 'linear':
            df = df.loc['linear'] + df.loc['ground']
        else:
            df = df.loc[args.property]
        base = df ['share']
        for col in df.columns:
            df[col] = df[col] / base
    else:
        df = pd.read_csv('report_time.csv', index_col='program')
        for col in df.columns:
            df[col] = pd.to_numeric(df[col], errors='coerce')
        df = df.dropna()

    fig1 = show_boxplot(df, ['share', 'as_sharing_noopt_mgu', 'as_sharing_noopt', 'as_sharing_opt'], args.property)
    fig2 = show_boxplot(df, ['shfrlin', 'as_shlin_noopt_mgu', 'as_shlin_noopt', 'as_shlin_opt_opt'], args.property)
    fig3 = show_boxplot(df, ['as_shlin2_noopt_mgu', 'as_shlin2_noopt', 'as_shlin2_opt'], args.property)
    if args.property == 'time':
        fig4 = show_boxplot(df, ['as_sharing_opt', 'as_shlin_opt_opt', 'as_shlin2_opt'], args.property)
    else:
        fig4 = show_boxplot(df, ['as_sharing_opt', 'as_shlin_opt_opt', 'as_shlin2_opt'], args.property)

    if args.output == '':
            plt.show()
    else:
        filename = args.output
        fig1.savefig(filename + '1.pdf', bbox_inches='tight', pad_inches=0)
        fig2.savefig(filename + '2.pdf', bbox_inches='tight', pad_inches=0)
        fig3.savefig(filename + '3.pdf', bbox_inches='tight', pad_inches=0)
        fig4.savefig(filename + '4.pdf', bbox_inches='tight', pad_inches=0)

    #show_graph(df, ['share', 'as_sharing_noopt_mgu', 'as_sharing_opt'])
    #show_graph(df, ['shfrlin', 'as_shlin_noopt_mgu', 'as_shlin_opt_opt'])
    #show_graph(df, ['as_shlin2_noopt_mgu', 'as_shlin2_opt'])
    #show_hist(df, ['share', 'as_sharing_noopt_mgu', 'as_sharing_noopt', 'as_sharing_opt'])

if __name__ == "__main__":
    main()
