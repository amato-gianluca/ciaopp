# Summary of the benchmarks

This directory contains the results of the analysis performed on 2026-01-27 using Ciao Prolog 1.25.0-m1.

## Differences with previous benchmarks

  - Memory usage has been explicitly limited to 24GB using the `prlimit` command. This is because
  the oom-killer was not consistent in its behaviour, and in new versions of Linux kills not
  only the `ciaoengine` but also the `analyze.sh` script. For this reason, when an analysis
  terminates with an out-of-memory error the exit code is now 1 instead of 137.

  - In the `flatten` and `serialise` benchmarks, the results for `share` and `shfrlin` have changed
  due to improvements in the official CiaoPP.

  - The analysis time of `reducer` with the domain of `as_shlin_opt_opt` is around 120 seconds. Therefore,
  the timeout tends to truncate the output file randomly. If the analysis is executed with an increased
  timeout, the results are similar to the old ones.
