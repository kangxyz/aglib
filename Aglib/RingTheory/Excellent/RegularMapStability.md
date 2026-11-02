# Bounded stability of actual regular maps

The source rings and field tests are in the same explicit universe u.
`regular_residueExtension_of_quasiFinite` uses the native finite residue
extension for arbitrary primes of a quasi-finite algebra, and transitivity
to apply the original regular-map test. All supplied coefficient actions
are retained. Here quasi-finite is the native fibre-finiteness property;
no finite-type hypothesis is inferred for an arbitrary localization.

`baseChange_of_finite` proves stability under finite algebra base change,
using native flat base change and tensor cancellation.
`localization_target` localizes the actual tested fibres and uses native
regularity under localization.
`localization_source` retains a supplied compatible localized-source action,
using native flatness over a localization and `algebraTensorEquiv`.

These laws are intended for the original finite-semilocal completion branch
comparison. They do not assert finite-type stability of G-rings or introduce
an alternative excellence predicate. They do not by themselves identify a
completed local branch with an original tensor/product factor.
