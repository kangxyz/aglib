# Degree-zero localization adapter

`DegreeZero.lean` specializes the native generic `higherExchangeZero` theorem
to the existing derived flat base-change map. Its premise is proved from the
original whole complex-unit equation; only exact flat-pullback units are
cancelled. It obtains

    j*(R0_f → f_*) ; beta = higherBeta_0 ; (R0_b → b_*).

Thus the higher-image stalk comparison in `Localization.lean` can be identified
with the original ordinary base-change mate used in `BaseChange.lean`.
Flatness of j, the actual Cartesian square, and the original scalar maps are
retained. The invertibility corollary additionally requires qcqs f and a
quasicoherent coefficient; no properness or finite map to the original base
is used. Compilation remains subject to the integrator's graph.
