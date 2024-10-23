# Useful options: -foutput_lang=raw -ftrace_fixp=trace

FILES="boyer.pl findall.pl sharing_experiments.pl shlin_experiments.pl shlin2_experiments.pl"
OPTIONS="-ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fshlin2_full_output=on"

for FILE in $FILES; do
    RESULTDIR="$(basename $FILE .pl)"
    mkdir -p "$RESULTDIR"
    rm  -f "$RESULTDIR"/*.pl

    ciaopp -o "$RESULTDIR"/as_shlin2_opt.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal
    ciaopp -o "$RESULTDIR"/as_shlin2_opt_mgu.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal -fas_use_match=no
    ciaopp -o "$RESULTDIR"/as_shlin2_noopt.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=off
    ciaopp -o "$RESULTDIR"/as_shlin2_noopt_mgu.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fas_use_match=no -fmgu_shlin2_optimize=off
    ciaopp -o "$RESULTDIR"/as_shlin_opt_opt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=optimal
    ciaopp -o "$RESULTDIR"/as_shlin_opt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=off
    ciaopp -o "$RESULTDIR"/as_shlin_noindcheck.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fmatch_shlin_optimize=off
    ciaopp -o "$RESULTDIR"/as_shlin_noopt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fmatch_shlin_optimize=off
    ciaopp -o "$RESULTDIR"/as_shlin_opt_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fas_use_match=no
    ciaopp -o "$RESULTDIR"/as_shlin_noindcheck_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fas_use_match=no
    ciaopp -o "$RESULTDIR"/as_shlin_noopt_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fas_use_match=no
    ciaopp -o "$RESULTDIR"/as_sharing_opt.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal
    ciaopp -o "$RESULTDIR"/as_sharing_noopt.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off
    ciaopp -o "$RESULTDIR"/as_sharing_opt_mgu.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal -fas_use_match=no
    ciaopp -o "$RESULTDIR"/as_sharing_noopt_mgu.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off -fas_use_match=no
    ciaopp -o "$RESULTDIR"/share.pl -A $FILE -fmodes=share_amgu $OPTIONS
    ciaopp -o "$RESULTDIR"/shfrlin.pl -A $FILE -fmodes=shfrlin_amgu $OPTIONS
done