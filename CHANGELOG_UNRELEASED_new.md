# Changelog (unreleased)

## [Unreleased]

### Added

- in `unstable.v`:
  + lemmas `oppr_itvNy`, `oppr_itvy`

- in `set_interval.v`:
  + lemmas `opp_preimage_itvbndy`, `opp_preimage_itvbndbnd`

- in `lebesgue_measure.v`:
  + lemma `lebesgue_measure_unique`

- in `lebesgue_integral_nonneg.v`:
  + lemmas `lebesgue_measureN`, `ge0_integral_pushforwardN`

- in `measurable_realfun.v`:
  + definition `min_mfun`

- in `random_variable.v`
  + lemmas `lebesgue_integral_pmf`, `cdf_measurable`, `ccdf_measurable`,
    `le0_expectation_cdf`

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_setU`

- in `measurable_realfun.v`:
  + lemmas `emeasurable_fun_itv_obnd_cbndP`, `emeasurable_fun_itv_bndo_bndcP`,
    `emeasurable_fun_itv_cc`

### Deprecated

- in `lebesgue_integral_nonneg.v`:
  + lemma integral_setU_EFin`

### Renamed

- in `lebesgue_integral_nonneg.v`:
  + `integral_setD1_EFin` -> `integral_setD1`

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`,
    `integral_itv_bndoo`

### Removed

- in `measurable_realfun.v`:
  + lemma `max_mfun_subproof` (has become a `Let`)

- in `simple_functions.v`:
  + definition `max_sfun`

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_setU` (was deprecated since version 1.0.1)



