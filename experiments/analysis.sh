#ciaopp -A prova.pl -fmodes=as_sharing -ftypes=none -foutput_lang=raw -ftrace_fixp=trace; cat prova_shlin_co.pl


ciaopp  -o as_shlin_opt.pl -A shlin_experiments.pl -fmodes=as_shlin -ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fmgu_shlin_optimize=noindcheck
ciaopp  -o as_shlin_noopt.pl -A shlin_experiments.pl -fmodes=as_shlin -ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fmgu_shlin_optimize=off
ciaopp  -o as_sharing_opt.pl -A shlin_experiments.pl -fmodes=as_sharing -ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fmgu_sh_optimize=on
ciaopp -o as_sharing_noopt.pl -A shlin_experiments.pl -fmodes=as_sharing -ftypes=none -fcollapse_ai_vers=off -fpp_info=on -fmgu_sh_optimize=off
ciaopp -o share.pl -A shlin_experiments.pl -fmodes=share_amgu -ftypes=none -fcollapse_ai_vers=off -fpp_info=on
ciaopp -o shfrlin.pl -A shlin_experiments.pl -fmodes=shfrlin_amgu -ftypes=none -fcollapse_ai_vers=off -fpp_info=on
