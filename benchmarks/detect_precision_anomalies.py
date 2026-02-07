#!/usr/bin/env python3

import pandas as pd
import sys

CONSTRAINTS = [
    [ 'as_shlin2_opt', 'as_shlin2_opt_mgu'],
    [ 'as_shlin2_opt', 'as_shlin2_noopt'],
    [ 'as_shlin2_noopt', 'as_shlin2_noopt_mgu'],
    [ 'as_shlin2_opt_mgu', 'as_shlin2_noopt_mgu'],

    [ 'as_shlin_opt_opt', 'as_shlin_opt'],
    [ 'as_shlin_opt', 'as_shlin_noindcheck'],
    [ 'as_shlin_noindcheck', 'as_shlin_noopt'],
    [ 'as_shlin_opt_opt', 'as_shlin_opt_mgu'],
    [ 'as_shlin_opt_mgu', 'as_shlin_noindcheck_mgu'],
    [ 'as_shlin_noindcheck_mgu', 'as_shlin_noopt_mgu'],

    [ 'as_sharing_opt', 'as_sharing_opt_mgu'],
    [ 'as_sharing_opt', 'as_sharing_noopt'],
    [ 'as_sharing_noopt', 'as_sharing_noopt_mgu'],
    [ 'as_sharing_opt_mgu', 'as_sharing_noopt_mgu'],

    [ 'as_shlin2_opt', 'as_shlin2_opt_mgu'],
    [ 'as_shlin_opt_opt', 'as_sharing_opt'],
    [ 'as_sharing_opt', 'share'],
]

def detect_mshare_anomalies(csv_file):
    """
    Detect anomalies.
    """
    df = pd.read_csv(csv_file)
    anomalies = []

    for col1, col2 in CONSTRAINTS:

        for idx, row in df.iterrows():
            property = row['property']
            val1 = row[col1]
            val2 = row[col2]

            # Skip rows with NaN values
            if pd.isna(val1) or pd.isna(val2):
                continue

            # Check for anomaly
            is_anomaly = val1 > val2 if property=='mshare' else val1 < val2

            if is_anomaly:
                anomalies.append({
                    'row_index': idx,
                    'property': property,
                    'program': row['program'],
                    'col1': col1,
                    'val1': val1,
                    'col2': col2,
                    'val2': val2,
                })

    # Report results
    if anomalies:
        print(f"Found {len(anomalies)} anomaly(ies):")
        print("-" * 80)
        for anomaly in anomalies:
            print(f"Row {anomaly['row_index']}: {anomaly['program']}")
            print(f"  property: {anomaly['property']}")
            print(f"  col1: {anomaly['col1']} -- {anomaly['val1']}")
            print(f"  col2: {anomaly['col2']} -- {anomaly['val2']}")
            print()
    else:
        print("No anomalies found")

    return anomalies

if __name__ == "__main__":
    csv_path = "results/report_precision.csv"
    anomalies = detect_mshare_anomalies(csv_path)
    sys.exit(0 if not anomalies else 1)
