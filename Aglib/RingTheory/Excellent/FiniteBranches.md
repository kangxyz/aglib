# Regular completion of finite-algebra branches

`AdicCompletion.FiniteSemilocal.tensorEquivOverAlgebra` upgrades the original
`tensorEquivRight` ring equivalence to the original finite-algebra coefficient
action. Its compatibility is exactly `tensorEquivRight_tmul_one`; the existing
completed branches and tensor/product comparison are not replaced.

`regularMap_completedBranch` assumes a Noetherian local ring R, a finite
R-algebra S, and regularity of the original completion map of R. It proves
regularity of the actual map from `Local R S q` to `Completed R S q` for each
native closed-fibre branch q. Neither R nor S is assumed a domain, and the
uncompleted selected local ring is not assumed finite over R.

The tensor algebra is regular over S by finite base change. Evaluation at q
is localization at the original idempotent, transported through the original
coefficient-compatible equivalence. Target localization and then source
localization give the claimed regular map. Residue-field tests at arbitrary
primes are retained through the bounded stability laws in `RegularMapStability`.
All source rings and finite residue-field tests have the same explicit
universe u.

This is finite-branch transfer, not full finite-type stability of G-rings.
Applying it to scheme normalization stalks still requires the original affine
and stalk/localization comparisons. It does not assert resolution existence.

`regularMap_localCompletion` states the result directly for a specified
original prime p of S over the maximal ideal of R. It uses `branchOfPrime`
and its original-ideal equation to eliminate the branch index, not a new
localization or completion model.
