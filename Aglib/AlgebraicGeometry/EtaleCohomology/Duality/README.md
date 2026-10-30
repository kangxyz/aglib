# Ext pairings for duality on the small étale site

Coefficients are genuine module sheaves `ModuleSheaf X Λ` over the constant ring sheaf of an
arbitrary ring `Λ : Type (u+1)`; sheaves of `ℤ/n`-modules (`Sh(X_et, n)`, Milne LEC p. 102) are
the case `Λ = ULift (ZMod n)`, for every `n`. `Ext` is Mathlib's `Abelian.Ext` in that category
and `HasExt` is a displayed size hypothesis (standard instances: `HasExt.standard`,
`SheafOfModules.hasExt`). The morphism `j : U ⟶ X` is étale (open immersions in the duality
application); the transport to `CompactSupport.H` and the direct-image third term take an open
immersion, and the inverse-image comparisons apply to arbitrary scheme morphisms, with `μ_n` requiring positive globally invertible `n`. Extension by
zero is `moduleLowerShriek j Λ` with
`moduleLowerShriekAdjunction : j_! ⊣ moduleInverseImage j Λ`.

| Source | Interface |
| --- | --- |
| [ModuleCohomology](../Coefficients/ModuleCohomology.lean) | `etaleModuleExtCohomologyAddEquivLargeScalars`: `Ext^q(Λ_X, G) ≃+ Sheaf.H (toSheaf G) q` among `Λ_X`-modules (Milne LEC p. 102), natural in `G` (`Sheaf.H.map`) and sending postcomposition with `hS.extClass` to `Sheaf.H.δ` of the underlying sequence. It retains independent module and abelian Ext universes; `moduleUnitExtAddEquiv_apply`, `_mk₀`, `_naturality` and `_connecting` describe this original map. |
| [LowerShriekExt](../Exceptional/Open/LowerShriekExt.lean) | `moduleLowerShriekExt` (`Functor.mapExtAddHom` of `j_!`) with Yoneda composition, `mk₀` and `extClass`; `moduleLowerShriekExtEquiv` (`Adjunction.extEquiv`): `Ext^q(j_! A, B) ≃+ Ext^q(A, j^* B)`, compatible with Yoneda composition on both sides. |
| [LowerShriekCohomology](LowerShriekCohomology.lean) | `moduleLowerShriekCohomologyAddEquiv`: `Ext^r(Λ_X, j_! F) ≃+ Sheaf.H ((etaleLowerShriek j).obj (toSheaf F)) r` on the original objects (for an open immersion into a complete curve, `H^r_c(U, F)` of Milne LEC p. 92), natural in `F` and sending the module connecting map of `j_!` of a short exact sequence to `Sheaf.H.δ` of the abelian extension by zero of the underlying sequence. |
| [YonedaPairing](YonedaPairing.lean) | `moduleLowerShriekPairing c e h = c.comp (e.mapExactFunctor j_!) h`: `H^r_c(U, F) × Ext^s(F, G) → H^t_c(U, G)` (Milne LEC p. 103, "The pairing"). Biadditive (`moduleLowerShriekPairingHom`); natural in `F` and `G`; connecting maps with sign `+1` against precomposition with `extClass` (Mathlib `Ext.contravariantSequence`) and `(-1)^(s+1)` against Mathlib's signed `Ext.δ`; `moduleLowerShriekPairingDualHom` into total degree `d ≥ r` (`d = 2` for curves) with its three squares. |
| [RootsOfUnity](../Kummer/RootsOfUnity.lean) | `moduleRootsOfUnity X n`: the sheaf `μ_n` as a module sheaf over the constant ring `ULift (ZMod n)`, with `moduleRootsOfUnityUnderlyingIso` to `GroupCohomology.Kummer.Coefficients.mu X n`. |
| [LowerShriekComposition](LowerShriekComposition.lean) | For étale `jV : V ⟶ U`, `jU : U ⟶ X`: `moduleLowerShriekCompAddEquiv : H^r_c(U, jV_! A) ≃+ H^r_c(V, A)` (postcomposition with `moduleLowerShriekCompIso`); the pairing on `U` with first argument there and second argument `e ∈ Ext^s_U(jV_! A, B)` is the pairing on `V` with `moduleLowerShriekExtEquiv jV e`, followed by `mk₀ (compIso.hom ≫ jU_!(ε_B))` (`moduleLowerShriekPairing_eq_comp_counit`, DualHom form `moduleLowerShriekPairingDualHom_eq_comp_counit`; basic case `moduleLowerShriekPairing_moduleLowerShriekExt`). With `moduleLocalization_shortExact` on `U` this is the compatibility of Milne LEC Thm 14.7, Step 2, p. 94. |
| [PairingTranspose](PairingTranspose.lean) | `moduleLowerShriekPairingTransposeHom : Ext^s(F, G) →+ (H^{d-s}_c(U, F) →+ H^d_c(U, G))`, Milne's direction `ψ` (p. 94), with its squares against coefficient maps, `extClass` (sign `+1`) and Mathlib's `Ext.δ` (sign `(-1)^(s+1)`). |
| [PairingRestriction](PairingRestriction.lean) | `moduleLowerShriekPairingTransposeHom_restriction`: for étale `jV : V ⟶ U`, `jU : U ⟶ X`, the square of `ψ` against restriction to `V` (`e ↦ moduleLowerShriekExtEquiv jV (ε_F^* e)`) and the extension maps `H_c(V, -|_V) → H_c(U, -)` (postcomposition with `mk₀ (compIso.hom ≫ jU_! ε)`): the middle square of Milne LEC Thm 14.7, Step 2, p. 94, before the trace. |
| [ZModLinear](ZModLinear.lean) | For `Λ = ULift (ZMod n)`: `n • 𝟙 F = 0` (`moduleSheaf_uLiftZMod_nsmul_id_eq_zero`), every `Ext^q(F, G)` and `CompactSupport.H j F₀ r` is killed by `n`, with the canonical `ZMod n`-module structures `moduleSheafExtZModModule`, `compactSupportZModModule` (named, for local instances); `ZMod n`-bilinear `moduleLowerShriekPairingDualLinearMap` and `moduleLowerShriekPairingTransposeLinearMap`. |
| [CompactSupportPairing](CompactSupportPairing.lean) | `compactSupportPairing : CompactSupport.H j F₀ r × Ext^s(F, G) → CompactSupport.H j G₀ (r+s)` through `moduleLowerShriekCohomologyAddEquiv` (open immersion `j`), biadditive, natural in `F` and `G` with `CompactSupport.H.map`, sign `+1` against `CompactSupport.δ`; `compactSupportRootsPairing` with values in `CompactSupport.H j (Kummer.Coefficients.mu U n)` through `moduleRootsOfUnityUnderlyingIso`. |
| [RootsOfUnityInverseImage](../Kummer/RootsOfUnityInverseImage.lean) | [Scalar forgetting](../Exceptional/Coefficients/ZMod.lean) is full for `ULift (ZMod n)` (`moduleSheaf_uLiftZMod_toSheaf_full`); `moduleRootsOfUnityInverseImageIso : j^* μ_{n,X} ≅ μ_{n,U}` among module sheaves, for any `j : U ⟶ X` and `0 < n` invertible on `X`, lifting `rootsPullbackIso` (`moduleRootsOfUnityInverseImageIso_underlying`). |
| [ModuleUnitUnderlying](../Exceptional/Coefficients/ModuleUnitUnderlying.lean) | `moduleUnitUnderlyingIso`: the constant abelian sheaf `Λ` is the underlying abelian sheaf of `Λ_X = moduleUnit X Λ`, by sheafifying the original constant-ring unit on sections (`moduleUnitConstantMap`, locally injective and locally surjective); for `ℤ/n`, `moduleUnitCoefficientIso` with `ConstantFinite.coefficient (ULift (ZMod n)) X`. |
| [LowerShriekDirectImage](LowerShriekDirectImage.lean) | `moduleLowerShriekDirectImageAddEquiv : Ext^q(Λ_X, jU_!(i_* M)) ≃+ H^q(Z, M₀)` for an open immersion `jU` with `i ≫ jU` a closed immersion (through `CompactSupport.directImageAddEquiv`, Stacks 0GJ1), and its vanishing for `q > 0` on point schemes with separably closed residue fields: the third term of the module compact-support sequence of `moduleLocalization_shortExact`. |
| [ModuleUnitInverseImage](../Exceptional/Coefficients/ModuleUnitInverseImage.lean) | `moduleUnitInverseImageIso : j^* (ℤ/n)_X ≅ (ℤ/n)_U` among module sheaves for any `j`, lifting `inverseImageConstantIso` through `moduleUnitUnderlyingIso` (`moduleUnitInverseImageIso_underlying`). |

The pairing specializes the [general Ext constructors](../../../Algebra/Homology/DerivedCategory/Ext/README.md) to module lower shriek and the unit. Compact-support transport uses the module/abelian comparison at its boundary.

The groups carry no `Λ`-linear structure from Mathlib's `Ext/Linear.lean`: the module-sheaf
categories have no `Linear` instance, so for a general `Λ` bilinearity is biadditivity. For
`Λ = ULift (ZMod n)` the groups are killed by `n`, and [ZModLinear](ZModLinear.lean) supplies
their canonical `ZMod n`-module structures as named declarations for local instances
(`moduleSheafExtZModModule`, `compactSupportZModModule`). [Trace](Trace.lean) identifies the original module Ext² with `ZMod n` for a
smooth proper geometrically connected curve over an algebraically closed field,
positive invertible `n` and finite closed complement. It compares the original
module/abelian and proper traces and gives the smaller-open square. The
normalization is Aglib's Kummer boundary; SGA torsor, connecting and cup/Yoneda
sign comparisons remain open. Finite-pushforward compatibility, sheaf-dual
comparison, degree-one and general-coefficient perfectness, purity and local cohomology remain open. It serves Poincaré duality for curves (Milne LEC Thm 14.7, p. 93, and Thm 14.20, p. 101).

[TracePairing](TracePairing.lean) composes the original linear Yoneda pairing
with normalized module trace. Its `moduleDualityMap` and
`moduleDualityTransposeMap` retain whole coefficient naturality, extension
class and signed original connecting squares, degree-zero source precomposition
and identity/trace normalization. [ConstantCoefficients](ConstantCoefficients.lean)
lifts the existing root comparison through scalar forgetting; on every
connected scheme and for positive `n`, unit endomorphisms and Ext⁰ are uniquely
scalar multiples of the original identity.

[ConstantPerfectness](ConstantPerfectness.lean) proves native perfectness for
the unit coefficient in compact-support degrees 0 and 2 and for their transposes.
The curve is smooth proper geometrically connected over an algebraically closed
field; the open immersion has finite closed complement, possibly empty; `n` is
positive and invertible, including composite levels and one, with the displayed
global-section level conditions and independent Ext universes. The public
statement chooses no basis or root. Degree-one constant perfectness, general
finite locally constant coefficients, purity, finite-pushforward compatibility
and SGA torsor, connecting, cup/Yoneda and Weil sign comparisons remain open.
