# Global Cartier purity with the original positive counit

This module constructs global degree-one concentration and positive purity
for a closed immersion `i:D→X` with locally rank-one original kernel ideal,
locally Noetherian ambient scheme, and quasicoherent coefficient `M`.
Coefficient regularity is monicity of the original canonical Cartier tensor
section `τ_M`. No concentration, principal cover, exact row, raw/positive
comparison or counit-compatibility premise is supplied.

The first step derives monicity of the original ideal action
`I⊗M→M` from monicity of `τ_M`. Tensoring by the genuine ideal line preserves
monomorphisms. The original section associator law, braiding naturality and
positive evaluation identify the resulting map with the original ideal
action. Only the ideal is a line bundle; the coefficient is arbitrary.

On an actual affine open `U`, the original ideal-section equivalence and a
regular generator `a` construct a genuine frame of `Γ(I,U)`. Its inverse
functional splits insertion of that generator into the first tensor factor.
The existing `moduleTensorSectionLinear_bijective_of_isAffine` retains the
literal original tensor-section map. Together with the original monic ideal
action on sections, it proves injectivity of multiplication by `a` on
`Γ(M,U)`. The original `affineChartΓIso` transports this result to precisely
the section module consumed by Principal, preserving its scalar action.
No coefficient frame is assumed or chosen.

The chart producer starts from
`exists_affine_regular_idealGenerator_of_isLocallyRankOne`. It uses the
original surjection `i.app U`, its actual kernel equality with `(a)`, and
`RingHom.quotientKerEquivOfSurjective`. Its induced spectrum isomorphism
retains the original quotient-map factorization. The original restriction
pullback square is transported through the specified affine `isoSpec` maps,
using `Scheme.Opens.toSpecΓ_naturality`; this gives actual quotient/fromSpec
cartesian squares. Their coverage follows from the original affine-open point
comparison and the pullback's actual point lifting. The chart data are
constructed internally, not passed to the global theorem.

Local Noetherianity supplies Noetherian rings on these affine opens. Principal proves vanishing away from degree one, and the original installed
`derivedClosedImmersionRightAdjointOpenHomologyIso` transports this vanishing
to the actual source restrictions. The native open-cover zero criterion gives
global concentration. Its first comparison is with the installed object's
own `H¹`; it does not assume the desired quotient is its heart.

The original global coefficient row was proved in the Purity parent.
The new purity map is the original installed single-derived adjoint of that
row's positive `extClass.hom`. `sectionExtensionMate_isIso`, applied
to the now-derived row and concentration, proves this particular map
invertible. The degree-one counit theorem is exactly the inverse original
adjunction applied to this map, equalling the original global row class.
The original single-shift and full faithfulness produce the unshifted native
degree-one isomorphism, and its homology gives the actual module-sheaf quotient
`i^*(I^dual⊗M)`.

The native convention places this quotient in degree one, equivalently the
cohomological shift `[-1]`. The coefficient and quotient module actions are
the original native actions. There is no coefficient-line orientation or
assumption that a canonical module is invertible.

This pair concerns Cartier adjunction, not CM canonical concentration or the
global curve Serre pairing. The finite/Serre identification of the particular
global boundary, hyperplane generation and final surface consequences remain
downstream. Equality with raw principal representatives and full positive
derived-open compatibility are not asserted or used as inputs.
