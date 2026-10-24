# Relative projective traces

[AffineTrace](AffineTrace.lean) provides the original normalized affine trace
with arbitrary quasicoherent coefficients. [Trace/Core](Trace/Core.lean)
constructs its actual derived scheme-base trace over a separated base, with
coefficient naturality and the native open restriction equation.

## Affine source

Let `R` be a commutative ring, let `e : ι ≃ Fin (n + 1)`, and let `N` be a
quasicoherent module sheaf on `Spec R`. For the actual structural map
`p : ProjectiveSpace R ι ⟶ Spec R`, the coefficient is the literal sheaf

`Ω_p(N) = (∧ⁿ Ω_p) ⊗ p* N`.

`projectiveAffineDifferentialTraceLinearEquiv` identifies its original degree
`n` cohomology with the original module of sections of `N`. The coordinate
finiteness instance is induced internally by `e`. There is no public `Fintype`
parameter and no Noetherianity or coefficient-flatness hypothesis. The statements
include dimension zero, zero/empty affine bases, and nonflat coefficients.

The construction uses the existing ordered determinant/twist comparison from
[DifferentialTrace](../DifferentialTrace.lean), the original
[coefficient residue trace](../Derived/Coefficients.lean), and the native tilde
counit. The following equations retain those maps:

- `_tilde_residue` identifies the trace on `tilde J` with the original coefficient
  residue trace after `projectiveDifferentialCoefficientsTwistingIso` and the
  original tilde unit, for every `R`-module `J`.
- `_unit` recovers the original differential residue trace through the native
  pullback-unit comparison and tensor right unitor.
- `_residue` sends the original differential Cech residue class of `r` to the
  original section represented by `r`.
- `_naturality` commutes with the actual coefficient morphism `N ⟶ N'`.
- `_open` commutes with the actual projective map of an open immersion of affine
  bases and the original restriction of coefficient sections.

`projectiveAffineDifferentialCoefficientsOpenMap` is the canonical coefficient
arrow in the last equation. Its `_eq_homEquiv` theorem identifies it with the
original restriction adjunction applied to the actual differential coefficient
restriction isomorphism.

## Coefficients on arbitrary scheme morphisms

`relativeTopDifferentialCoefficientsFunctor p n` defines the same literal
coefficient functor for every scheme morphism `p` and natural number `n`.
`relativeTopDifferentialRestrictionIso` and
`relativeTopDifferentialCoefficientsRestrictionIso` give its native comparisons
on commuting squares with open source and base maps.
`relativeTopDifferentialCoefficientsUnitIso` is the native structure-coefficient
unitor. `relativeTopDifferentialCoefficientsRestrictionIso_unit` proves its exact
compatibility with those restriction maps.

## Scheme-base construction and current consumers

For a supplied Cartesian pullback of `ProjectiveSpace R ι ⟶ Spec R` over a
separated scheme `Y`, [Trace/Core](Trace/Core.lean) transports the affine maps
through the actual affine pullback isomorphism, proves the overlap equation,
and glues degree `n` higher-image module morphisms. The native `HomToSingle`
comparison reconstructs the arrow from the installed `RpPlus`, followed by
full-category inclusion, to `single_n N`. Its affine sections are the original
polynomial differential trace, with arbitrary quasicoherent `N` and no
Noetherianity or flatness assumption.

The public [Trace](Trace.lean) facade exposes this completed construction.
The affine formula `relativeProjectiveHigherTrace_affine` identifies its value
with the same original affine trace. [Trace/Residue](Trace/Residue.lean) gives
the coefficient-residue formula, while AffineTrace's coefficient naturality,
unit and residue-class laws give its original unit and scalar normalization.
The actual derived trace has the corresponding affine normalization in Core.
Its derived open-restriction equation is proved in
[Comparison/OpenTrace](Comparison/OpenTrace.lean).
These are composable proved equations; no compatibility premise is supplied.

[Comparison](Comparison.lean) applies this same trace after the actual derived
pushforward of the original Ext arrow. [ClosedEmbedding](ClosedEmbedding.lean)
transfers that comparison through the installed closed-immersion right
adjoint and native pushforward-composition isomorphism.
[ClosedEmbedding/Structural](ClosedEmbedding/Structural.lean) proves linearity
for every supplied structural scalar action, independently of coherent
bijectivity. These constructions retain arbitrary quasicoherent coefficients.

[Coherent](Coherent.lean) proves that the literal comparison is bijective in
every natural Ext degree over a Noetherian separated base, for a native
`affineLocallyFiniteType` source and arbitrary quasicoherent coefficients.
[ClosedEmbedding/Linear](ClosedEmbedding/Linear.lean) gives its linear
equivalence through the chosen closed embedding, with the same forward map and
the actual right-adjoint coefficient object. Neither coefficient flatness nor
Noetherianity of the projective presentation ring is required.

The target has shift `q - n`; no vanishing of higher Ext over a singular base
is asserted. [Smooth/Trace](Smooth/Trace.lean) transports the same original map
through the actual [canonical identification](../Canonical.lean). Its trace
identity holds in every natural Ext degree over a separated base, without
Noetherianity or coherence needed for construction. [Smooth](Smooth.lean) proves
the corresponding coherent linear duality over a Noetherian separated base,
with the explicit formula: derived pushforward of the original Ext arrow,
followed by that one trace. The integer-indexed canonical identification and
the actual empty-source argument avoid a global `d ≤ n` condition.

## Chosen-embedding curve and normal-surface interfaces

[CohenMacaulayCurve](CohenMacaulayCurve.md) constructs concentration and the
canonical module for an actual closed embedding over an arbitrary field.
At every closed stalk it requires a regular element with maximal principal
radical. Nonreduced and non-Gorenstein sources are allowed. The canonical
degree is the integer `(n : ℤ) - 1`.
[Coefficients](CohenMacaulayCurve/Coefficients.md) retains an actual finite
one-dimensional coefficient module and its own canonical homology, including
the intrinsic derived-residue line, without choosing an orientation.

[Unit-coefficient Serre duality](CohenMacaulayCurve/Serre.md) retains the same
closed-stalk condition and `1 ≤ n`, with coherent-source bijectivity and
the original trace and positive Yoneda pairing. Its
[Derived](CohenMacaulayCurve/Serre/Derived.md),
[Transport](CohenMacaulayCurve/Serre/Transport.md),
[Pairing](CohenMacaulayCurve/Serre/Pairing.md),
[Trace](CohenMacaulayCurve/Serre/Trace.md) and
[Comparison](CohenMacaulayCurve/Serre/Comparison.md) providers preserve the
native single/shift maps, structural section one and original additive
comparison. [Coefficient affine model](CohenMacaulayCurve/Coefficients/Serre/Affine.md)
proves the generic map and evaluation laws for arbitrary specified field
modules. It does not supply full coefficient-valued Serre duality.
[Enlargement](CohenMacaulayCurve/Enlargement.md) constructs finite-support
row enlargement from supplied trace-compatible coherent-source duality;
the geometric hyperplane and those coefficient comparisons remain inputs.

[NormalSurface](NormalSurface.md) constructs chosen-embedding concentration
for a normal integral source of dimension at most two over a regular local
domain, with dominant finite original function-field map. Inseparability is
allowed and the canonical module is not assumed invertible.
[Trace](NormalSurface/Trace.md) retains its original canonical-section trace.
[Cohomology](NormalSurface/Cohomology.md) compares original canonical
cohomology with the native A-linear derived dual.
[UnitTrace](NormalSurface/Cohomology/UnitTrace.md) identifies the original
dual unit with the section trace for a finite injective local map from a
regular local surface base to a normal Noetherian local surface domain,
retaining the supplied resolutions and structural triangle. These are
chosen-embedding interfaces; global integral trace and surface-to-curve
canonical restriction remain separate obligations.

[CartierRegularity](NormalSurface/CartierRegularity.md) proves that every
nonzero original stalk element acts regularly on the actual normal-surface
canonical stalk. It derives monicity of the original Cartier tensor section
for a closed immersion with locally rank-one kernel ideal. The original
normal integral source, dimension bound, regular local base, finite projective
indexing and dominant finite generic-image map remain those of concentration;
no canonical freeness or Gorenstein premise is added.
[CartierRestriction/Transport](NormalSurface/CartierRestriction/Transport.md)
transports original Serre maps through supplied canonical reconstructions
and native affine sections, retaining integer degree `r-d`, coefficient
comparisons and source Ext-composition laws. Bijectivity keeps the Noetherian
base and affine-locally-finite-type source hypotheses. These are suppliers
to full canonical restriction and its counit comparison, which remain open.
