# Normal completion at an original prime of a finite G-ring algebra

`AdicCompletion.normalDomain_of_finite_of_isGRing` assumes a finite algebra
R → S over a genuine G-ring R and an original prime q of S whose actual
local ring is a normal domain of dimension two. It proves both domainhood
and integral closedness of that local ring's literal maximal-adic completion.
Global normality or domainhood of S is not required.

The proof localizes R at the contraction p and localizes S at the images of
p's complement. This localized algebra is finite over R_p; the further
localization at the selected branch is not assumed finite. The exact component
`hG.2 p` supplies the regular original completion map, and `FiniteBranches`
transfers it to the actual branch.

The original `atPrimeBasePrimeComplEquiv` identifies that branch with S_q.
Normality, domainhood, and dimension are transported through this equivalence,
then the bounded normal-completion theorem applies. `congrRingEquiv` and the
proved maximal-ideal equation transfer both completion conclusions back to
the original S_q completion. No untracked replacement normal or valuation
model is used.

The source universe is explicit and shared. This is the bounded finite-map
consumer needed for normalization stalks; it does not assert general
finite-type G-ring stability, Nagata/N-2, or resolution existence.
