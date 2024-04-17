#ciaopp -A prova.pl -fmodes=as_sharing -ftypes=none -foutput_lang=raw -ftrace_fixp=trace; cat prova_shlin_co.pl
OPTIONS="-ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fshlin2_full_output=on"
FILES="boyer.pl browse.pl crypt.pl derive.pl divide10.pl eval.pl fast_mu.pl fib.pl log10.pl meta_qsort.pl
       moded_path.pl mu.pl nand.pl nreverse.pl ops8.pl perfect.pl pingpong.pl poly_10.pl prover.pl qsort.pl
       queens_8.pl query.pl sendmore.pl sieve.pl tak.pl times10.pl"

FILES="boyer.pl"

for FILE in $FILES; do
    RESULTDIR="results/$(basename $FILE .pl)"
    mkdir -p "$RESULTDIR"
    rm -p $FILE.log
    #rm -f "$RESULTDIR"/*.pl


    ciaopp -o "$RESULTDIR"/as_shlin2_opt.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin2_opt_mgu.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal -fas_use_match=no 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin2_noopt.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=off 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin2_noopt_mgu.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fas_use_match=no -fmgu_shlin2_optimize=off 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_opt_opt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=optimal 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_opt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=off 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_noindcheck.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fmatch_shlin_optimize=off 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_noopt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fmatch_shlin_optimize=off 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_opt_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fas_use_match=no 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_noindcheck_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fas_use_match=no 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_shlin_noopt_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fas_use_match=no 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_sharing_opt.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_sharing_noopt.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_sharing_opt_mgu.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal -fas_use_match=no 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/as_sharing_noopt_mgu.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off -fas_use_match=no 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/share.pl -A $FILE -fmodes=share_amgu $OPTIONS 2>&1 | tee -a $FILE.log
    ciaopp -o "$RESULTDIR"/shfrlin.pl -A $FILE -fmodes=shfrlin_amgu $OPTIONS 2>&1 | tee -a $FILE.log
done
