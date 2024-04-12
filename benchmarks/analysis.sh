#ciaopp -A prova.pl -fmodes=as_sharing -ftypes=none -foutput_lang=raw -ftrace_fixp=trace; cat prova_shlin_co.pl

FILE=boyer.pl
RESULTDIR=results/$(basename $FILE .pl)
mkdir -p $RESULTDIR
#rm $RESULTDIR/*.pl

OPTIONS="-ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fshlin2_full_output=off"

# ciaopp -o $RESULTDIR/as_shlin2_opt.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal
# ciaopp -o $RESULTDIR/as_shlin2_opt_mgu.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=optimal -fextend_implementation=mgu
# ciaopp -o $RESULTDIR/as_shlin2.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fmgu_shlin2_optimize=off
# ciaopp -o $RESULTDIR/as_shlin2_mgu.pl -A $FILE -fmodes=as_shlin2 $OPTIONS -fextend_implementation=mgu -fmgu_shlin2_optimize=off
# ciaopp -o $RESULTDIR/as_shlin_optopt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=optimal
# ciaopp -o $RESULTDIR/as_shlin_opt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fmatch_shlin_optimize=off
# ciaopp -o $RESULTDIR/as_shlin_noindcheck.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fmatch_shlin_optimize=off
# ciaopp -o $RESULTDIR/as_shlin_noopt.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fmatch_shlin_optimize=off
# ciaopp -o $RESULTDIR/as_shlin_opt_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=optimal -fextend_implementation=mgu
# ciaopp -o $RESULTDIR/as_shlin_noindcheck_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=noindcheck -fextend_implementation=mgu
# ciaopp -o $RESULTDIR/as_shlin_noopt_mgu.pl -A $FILE -fmodes=as_shlin $OPTIONS -fmgu_shlin_optimize=off -fextend_implementation=mgu
ciaopp -o $RESULTDIR/as_sharing_opt.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal
# ciaopp -o $RESULTDIR/as_sharing_noopt.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off
# ciaopp -o $RESULTDIR/as_sharing_opt_mgu.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=optimal -fextend_implementation=mgu
# ciaopp -o $RESULTDIR/as_sharing_noopt_mgu.pl -A $FILE -fmodes=as_sharing $OPTIONS -fmgu_sh_optimize=off -fextend_implementation=mgu
# ciaopp -o $RESULTDIR/share.pl -A $FILE -fmodes=share_amgu $OPTIONS
# ciaopp -o $RESULTDIR/shfrlin.pl -A $FILE -fmodes=shfrlin_amgu $OPTIONS