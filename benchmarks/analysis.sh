#!/bin/bash

#ciaopp -A prova.pl -fmodes=as_sharing -ftypes=none -foutput_lang=raw -ftrace_fixp=trace; cat prova_shlin_co.pl
OPTIONS="-ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fshlin2_full_output=on"
TIMEOUT=2m
FILES="boyer.pl browse.pl chat_parser.pl crypt.pl derive.pl divide10.pl eval.pl fast_mu.pl fib.pl flatten.pl log10.pl
       meta_qsort.pl moded_path.pl mu.pl nand.pl nreverse.pl ops8.pl perfect.pl pingpong.pl poly_10.pl prover.pl
       qsort.pl queens_8.pl query.pl reducer.pl sendmore.pl serialise.pl sieve.pl simple_analyzer.pl tak.pl times10.pl
       unify.pl zebra.pl"

# OTHER BENCHMARKS:
# det.pl has syntax errors
# queens_clpfd.pl uses CLP[FD] which is not supported

analyze() {
    FILE=$1
    CONFIGURATION=$2

    echo "START ANALYSIS -- CONFIGURATION: $CONFIGURATION" | tee -a "$RESULTDIR/log"
    shift 2
    timeout $TIMEOUT ciaopp -o "$RESULTDIR/$CONFIGURATION.pl" -A $FILE $@ 2>&1 | tee -a "$RESULTDIR/log"
    RES=${PIPESTATUS[0]}
    echo "END ANALYSIS -- EXIT CODE: $RES" | tee -a "$RESULTDIR/log"
}

for FILE in $FILES; do
    RESULTDIR="results/$(basename $FILE .pl)"
    mkdir -p "$RESULTDIR"
    rm -f "$RESULTDIR/log"
    #rm -f "$RESULTDIR"/*.pl

    analyze "$FILE" as_shlin2_opt           -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal
    analyze "$FILE" as_shlin2_opt_mgu       -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal -fas_use_match=no
    analyze "$FILE" as_shlin2_noopt         -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=off
    analyze "$FILE" as_shlin2_noopt_mgu     -fmodes=as_shlin2 $OPTIONS -fas_use_match=no -fmgu_shlin2_optimize=off
    analyze "$FILE" as_shlin_opt_opt        -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=optimal
    analyze "$FILE" as_shlin_opt            -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=off
    analyze "$FILE" as_shlin_noindcheck     -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fmatch_shlin_optimize=off
    analyze "$FILE" as_shlin_noopt          -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fmatch_shlin_optimize=off
    analyze "$FILE" as_shlin_opt_mgu        -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fas_use_match=no
    analyze "$FILE" as_shlin_noindcheck_mgu -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fas_use_match=no
    analyze "$FILE" as_shlin_noopt_mgu      -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fas_use_match=no
    analyze "$FILE" as_sharing_opt          -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal
    analyze "$FILE" as_sharing_noopt        -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off
    analyze "$FILE" as_sharing_opt_mgu      -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal -fas_use_match=no
    analyze "$FILE" as_sharing_noopt_mgu    -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off -fas_use_match=no
    analyze "$FILE" share                   -fmodes=share_amgu $OPTIONS
    analyze "$FILE" shfrlin                 -fmodes=shfrlin_amgu $OPTIONS
done
