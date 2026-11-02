# Algebraic differentials over the original expanded coefficient base

Let `k` be a field of prime characteristic `p`. Every series base in this
module acts through `FiniteCoefficientExpansion.scalarMap`: the original
coefficient inclusion is followed by `expand p`, sending the two base
variables to the pth powers of the original variables. `scalarAlgebra`
is installed explicitly in the differential statements and constructions.

The module constructs two ordinary algebraic Kähler bases:

- `twoVariableBasis`, when the original coefficient-field map `E → k`
  is surjective, has ordered values `du, dv`. Its coordinates on `df` are
  the two original formal partial derivatives.
- `threeVariableBasis`, from an actual coefficient power basis
  `1,c,…,c^(p−1)` and an actual `E`-derivation with value one at `c`, has
  ordered values `dc, du, dv`. The coefficient coordinate is first, followed
  by the two original formal partial derivatives.

The scalar map is retained when the spatial derivatives are repackaged
over the expanded base. Their vanishing on that base follows coefficientwise
from p-divisibility of exponents in characteristic p. The coefficient
derivation comes from the sibling `Derivation` module. The given coefficient
and spatial derivations form the identity matrix on the original generators.

`eq_top_of_coefficientBasis_mem` uses the passed finite series basis and
its actual finite reconstruction to prove algebraic generation. Thus the
generation assertion concerns all formal series, including series with
infinitely many distinct coefficients. This generation step needs no
characteristic assumption; characteristic p enters the derivative step.
The Kähler construction uses
`basisOfDerivations` and concerns all algebraic derivations; no completed
or continuous differential module is substituted.

`nonPowerDifferentialBasis` instantiates the three-generator construction
with the actual field, coefficient, monic presentation, and power basis
produced by `NonPowerComplement`. Its coefficient derivation is
`pureDegreePDerivation` of that same presentation, with value one at the
original coefficient. No desired differential basis or nonzero differential
is an input to this specialization.

For a given series `f` that is not a pth power, `exists_singleSeries_base`
constructs the needed alternative. If a nonzero coefficient has an exponent
not divisible by p, the top subfield of `k` and a spatial derivative detect
`df`. Otherwise a coefficient lies outside the literal Frobenius image:
if all coefficients lay in that image, `exists_pow_eq_of_coeff` would
construct a root series coefficientwise. The theorem chooses a maximal
avoiding subfield for that actual coefficient and proves nonzero `df` by
the coefficient derivation's value one. The first branch has the constructed
rank-two basis; the second has `nonPowerDifferentialBasis` of rank three.
These choices are made from the fixed input series and can be held fixed
through the later modification argument.

`twoVariable_finrank` and `threeVariable_finrank` record the ranks. The
exterior-basis theorems identify actual ordered wedges of the original
generator differentials. Their coordinate formulas are determinants of
the actual derivative matrix, with rows indexed by the given series and
columns ordered by the specified increasing subset of generator indices.
This fixes the coefficient-first orientation; it does not choose an
unrelated volume form.

`KaehlerDifferential.map_D_ne_zero_of_basis_localization` transports a
proved nonzero differential through an actual localization square. Its
hypotheses specify both localization structures, the original commuting
scalar maps, the ordinary Kähler basis, and nonzero images of denominators.
The proof uses the literal Kähler map and proves its injectivity by basis
coordinates. Instantiating these structures with the original fraction
fields is supplied by the sibling FractionRing leaf, whose direct basis
transport preserves Λ. This theorem does not assume that an unrelated field
replacement gives that square.

The mathematical basis is the independently reviewed single-series packet
SHA256 `2f1719be373003ddd48f5aa3ca3c340a07c6028243056f5e8678c855f9b4219c`,
and the finite-generation/dual-derivation continuation
`83273e8842fe2ba61a5513c020c38c358b7e857b15bcab2fa035ae505faca4e7`.
The current consumer is the entrance to the purely inseparable degree-p
B7 argument. The fixed-p-basis family/intersection theorem has a separate
identity and is not replaced by this single-series construction. Higher
trace, dualizing normalization, and the uniform cohomology bound remain
downstream.

The historical source basis was release HEAD
`f27c5fa9b8f76147e16caacf52f56f26eabddb87`, Lean 4.34.1, and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Whole-module compiler results
belong to the principal's shared native batch; this document does not
infer them from the proof scripts.

## Unified finite entrance

`exists_singleSeries_finite_basis` chooses a subfield E and positive rank r
(equal to 2 or 3 in its proof), a finite module structure for A over the
expanded base, an actual ordinary differential basis, and nonzero df. The
hypothesis is that f has no pth-power root in A; in the degree-p application,
nonexistence of a root in the actual fraction field implies this hypothesis.
The E choice occurs before any model. The algebra map from E[[u,v]] is the
coefficient inclusion followed by p-expansion, so its image is exactly
E[[u^p,v^p]], not the constant field E. The finite basis also gives freeness,
finite presentation over Noetherian A, and finite raw exterior powers.

## Current compilation evidence

On baseline `7d071440653407d30fd41d8dbbafce1673a3039b`, the guarded native
wave1 graph freshly built this leaf in 6.6 seconds on 2026-10-29. Its Lean
source SHA256 is
`47d11d6139cb651e3ad298ac44579a01ab6c1ef4d92f36f459cb192b6dba4661`.
The root-owned log is `surface-resolution-state/build-wave1.log` outside
the source tree. This is compilation coverage only: the other trace leaves,
package lint, production axiom audit and endpoint review are separate.
