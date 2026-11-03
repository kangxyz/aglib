# The original normal-surface canonical restriction

Source: [CartierRestriction.lean](CartierRestriction.lean).

The target is the actual restriction formula

`i*ω_X ≅ Ω_E(V) ⊗ i*I`,

where `I=idealModule i` is the original Cartier kernel, `ω_X` is the own
normal-surface canonical homology, and `Ω_E(V)` is the own chosen-embedding
coefficient canonical homology on the full Cartier curve. The coefficient
`V=ModuleCat.derivedResidueCoefficientLine R k` is the actual degree-two
homology of native derived coinduction along the original finite local map
from the regular local base. No orientation `V≅k` is chosen. The support may
be nonreduced, and the canonical modules need not be invertible.

The generic producer retains the accepted actual normal-surface data: a
regular local domain `R`, its dimension-two equality, a finite local map to
the field `k`, the chosen closed surface embedding with its dominant structural
map and finite original generic field map, normal stalks and global dimension
at most two, the actual locally rank-one Cartier ideal, and a chosen closed
curve embedding of positive ambient dimension. The original structural
triangle and ambient stalk dimension two at closed curve points are geometric
inputs. They are not canonical-module or map-compatibility assumptions.

At each such closed point, an actual local ideal frame produces a prescribed
regular generator of the kernel of the original stalk surjection. The normal
two-dimensional parameter-pair theorem produces a second parameter. Its image
in the literal quotient is regular and has maximal-primary principal ideal.
This derives the precise input of coefficient-valued curve concentration,
including for nonreduced quotients.

The coefficient regularity required by Cartier purity is supplied by the
existing `normalSurfaceCanonical_cartierSection_mono`, applied to the own
canonical homology. It is not an additional premise. The resulting Cartier
Ext map sends `x` to its actual exact pushforward followed by the positive
extension class of `cartierCoefficientSequence_shortExact`. Its degree-zero
identity is that very extension class. Bijectivity uses the installed positive
Cartier mate and the original closed adjunction's source-composition law.

The surface and curve Serre factors use the original relative coefficient
functor, the own-homology-normalized canonical reconstructions, original affine
derived sections and their unit comparisons. The surface output has degree
`r+1`; the curve output has integer degree `r-1`. The native finite-local
restriction/coinduction adjunction converts exactly those two targets. The
structural triangle derives the equality of scalar maps used by the original
derived sections restriction isomorphism. No finite-pushforward right adjoint
on all sheaves is asserted.

`normalSurfaceCartierExtEquiv` is the composition of those original maps.
Its source Yoneda law is proved for arbitrary nonnegative Ext degrees.
Coherence of the actual Cartier quotient and curve canonical module is
derived before they enter the degree-zero Yoneda argument. The resulting
`normalSurfaceCartierQuotientIso` is characterized by

`T_F^r(x) = x.comp (Ext.mk₀ θ.hom)`.

Thus the degree-zero sheaf isomorphism and the higher Ext comparison are the
same construction. Their arrows are actual module-sheaf morphisms, retaining
the original structure-sheaf and field actions.

`normalSurfaceCartierUnitTrace` evaluates at the original field unit, retaining
the full restricted `k`-unit rather than only its precomposition with `R→k`.
`normalSurfaceCartierUnitTrace_counit` expresses the same identity through
`residueLineTrace`, whose installed normalization is the original shifted
coinduction counit after the own degree-two reconstruction.
`normalSurfaceCartierCurveTrace` evaluates the corresponding native
`Hom_k(k,V)` arrow at one using the original zero-shift comparison. It takes
values in the literal intrinsic module `V`.

Finally, `normalSurfaceCartierRestrictionIso` applies the installed positive
Cartier cancellation isomorphism, the original pullback tensor map, and
`θ` tensored with the identity on the same `i*I`. This fixes the sign of the
twist without a separate dual-sheaf base-change choice.

The ordinary specialization uses the literal existing
`exceptionalCurve A hd`, `exceptionalCurveInclusion A hd` and
`exceptionalStructureMap A hd`. It derives normal stalks from ordinary
rational-blowup normality, the global dimension bound and closed-stalk dimension
from the exceptional geometry producer, and Cartierness from the original
blowup datum. The finite local residue map is the original composite
`R→A→A/m`. The accepted chosen surface embedding, its structural triangle,
dominance and finite original generic field map remain the same explicit
surface inputs. No new canonical or curve-CM condition is added.

`exists_exceptionalCanonicalRestriction` obtains the actual positive-dimensional
curve embedding and matched positive `O(1)` from the padded tautological row.
The output twist is the literal `exceptionalLine`, namely `i*I`. It never
replaces the exceptional scheme by its reduction.

This is the restriction step. Canonical generation, Gorensteinness,
triviality of the surface canonical module, Hilbert slope two and RDP conclusions
are separate consumers. In particular, a later slope-two or triviality argument
must retain its required nonregularity or degree-at-least-two input.

## Original finite-base and stalk inputs

Source provenance: the historical candidate used base
`7d071440653407d30fd41d8dbbafce1673a3039b`.
The generic finite base leg is `R → k`; the statement has no finiteness
assumption on `R → O_(X,x)`. Closed surface-stalk dimension two is explicit
and supplies the actual curve CM parameters through the original Cartier
kernel, rather than through reduction or a smooth-curve replacement.

## Equality to the coefficient Serre parent's original maps

The added `normalSurfaceCartierCurveSerreMap_eq_coefficient` identifies the
transported curve functional with the literal composite of
`cmCurveCoefficientSerreDerivedLinearMap` and
`cmCurveCoefficientSerreModuleHom`. The proof compares the actual affine
functor isomorphism on source and target, using its native shift naturality
and `cmCurveCoefficientSerreAffineDerived_coefficient`. The purity inputs
use the same own-homology reconstruction; the natural-degree reindex is
identified by `(m-1)+r = r+(m-1)`, with no truncation of a negative index.

`normalSurfaceCartierCurveTrace_eq_coefficient` then states

`CartierTrace(β) = coefficientSerreTrace(H¹-class(β · θ))`.

Here `H¹-class` is the original `moduleExtCohomologyMap`, and `θ` is the same
coherent-Yoneda quotient isomorphism. The proof identifies the native single
preimage, the original zero-shift normalization and the same structural-unit
evaluation; it does not replace either trace by an arbitrarily normalized
functional.

The scalar-sections, reconstruction and Serre-transport helper definitions used in
exposed public restriction maps are public interfaces with unchanged native bodies.
The positive Cartier Ext map is the composition of the native exact-functor
additive Ext map and postcomposition by the original Cartier extension class.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalizedExceptionalCanonicalVanishing](LocalizedExceptionalCanonicalVanishing.md).
