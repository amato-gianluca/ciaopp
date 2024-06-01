#ciaopp -A prova.pl -fmodes=as_sharing -ftypes=none -foutput_lang=raw -ftrace_fixp=trace; cat prova_shlin_co.pl
OPTIONS="-ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fshlin2_full_output=on"
TIMEOUT=2m
FILES="boyer.pl browse.pl chat_parser.pl crypt.pl derive.pl divide10.pl eval.pl fast_mu.pl fib.pl log10.pl
       meta_qsort.pl moded_path.pl mu.pl nand.pl nreverse.pl ops8.pl perfect.pl pingpong.pl poly_10.pl prover.pl
       qsort.pl queens_8.pl query.pl reducer.pl sendmore.pl serialise.pl sieve.pl tak.pl times10.pl"

# OTHER BENCHMARKS:
# det.pl has syntax errors
# flatten.pl crashes the analyzer in some domains
# queens_clpfd.pl uses CLP[FD] which is not supported
# simple_analyze crashes the analyzer in some domains
# unify crashes the analyzer in some domains
# zebra crashes the analyzer in some domains

analyze() {
    FILE=$1
    OUTFILE=$2

    echo "Analyzing with aim: $OUTFILE" | tee -a "$RESULTDIR/log"
    shift 2
    timeout $TIMEOUT ciaopp -o "$RESULTDIR/$OUTFILE" -A $FILE $@ 2>&1 | tee -a "$RESULTDIR/log"
}

for FILE in $FILES; do
    RESULTDIR="results/$(basename $FILE .pl)"
    mkdir -p "$RESULTDIR"
    rm -f $FILE.log
    #rm -f "$RESULTDIR"/*.pl

    analyze "$FILE" as_shlin2_opt.pl           -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal
    analyze "$FILE" as_shlin2_opt_mgu.pl       -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal -fas_use_match=no
    analyze "$FILE" as_shlin2_noopt.pl         -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=off
    analyze "$FILE" as_shlin2_noopt_mgu.pl     -fmodes=as_shlin2 $OPTIONS -fas_use_match=no -fmgu_shlin2_optimize=off
    analyze "$FILE" as_shlin_opt_opt.pl        -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=optimal
    analyze "$FILE" as_shlin_opt.pl            -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=off
    analyze "$FILE" as_shlin_noindcheck.pl     -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fmatch_shlin_optimize=off
    analyze "$FILE" as_shlin_noopt.pl          -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fmatch_shlin_optimize=off
    analyze "$FILE" as_shlin_opt_mgu.pl        -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fas_use_match=no
    analyze "$FILE" as_shlin_noindcheck_mgu.pl -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fas_use_match=no
    analyze "$FILE" as_shlin_noopt_mgu.pl      -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fas_use_match=no
    analyze "$FILE" as_sharing_opt.pl          -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal
    analyze "$FILE" as_sharing_noopt.pl        -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off
    analyze "$FILE" as_sharing_opt_mgu.pl      -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal -fas_use_match=no
    analyze "$FILE" as_sharing_noopt_mgu.pl    -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off -fas_use_match=no
    analyze "$FILE" share.pl                   -fmodes=share_amgu $OPTIONS
    analyze "$FILE" shfrlin.pl                 -fmodes=shfrlin_amgu $OPTIONS
done
