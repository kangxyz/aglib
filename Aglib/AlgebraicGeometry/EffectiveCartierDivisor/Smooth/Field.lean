/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locality
public import Aglib.RingTheory.KrullDimension.RegularQuotient
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Charts
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.HopkinsLevitzki
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Actual Cartier ideals on smooth relative curves over a field

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/CartierLocality.lean`, SHA-256
  `d11c4ffb39327cd751cb517541e51344ca708630381facd0620868347b548718`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

/-- The spectral smooth-field input: every maximal localization is regular
of dimension one, without any connectedness or integrality assumption. -/
theorem smoothField_maximal_localization_regular_dimension_one
    (K : Type u) [Field K] (R : CommRingCat.{u})
    (p : Spec R ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (P : Ideal R) [P.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime P) ∧
      ringKrullDim (Localization.AtPrime P) = 1 := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let x : Spec R := ⟨P, inferInstance⟩
  let := smoothFieldRegularity K (Spec R) p inferInstance x
  let e := (Spec.stalkIso R x).commRingCatIsoToRingEquiv
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact smoothClosedPointDimension K (Spec R) p 1 inferInstance x
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr inferInstance)

/-- Every Artinian closed subscheme of a smooth affine field curve has an
invertible actual kernel ideal. -/
theorem smoothField_spectral_artinian_ideal
    (K : Type u) [Field K] {R S : CommRingCat.{u}}
    (p : Spec R ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (φ : R ⟶ S) (hsurj : Function.Surjective φ.hom) [IsArtinianRing S] :
    IsLocallyRankOne (Spec R) (idealModule (Spec.map φ)) := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  exact artinianQuotientIdeal_isLocallyRankOne φ hsurj
    (smoothField_maximal_localization_regular_dimension_one K R p)

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X D : Scheme.{u}}

/-- The affine smooth-field statement for any locally Artinian closed subscheme. -/
theorem smoothField_affine_artinian_ideal
    (K : Type u) [Field K] [IsAffine X] [IsLocallyArtinian D]
    (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (i : D ⟶ X) [IsClosedImmersion i] :
    IsLocallyRankOne X (idealModule i) := by
  let : IsAffine D := isAffine_of_isAffineHom i
  let : SmoothOfRelativeDimension 1 (X.isoSpec.inv ≫ p) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (X.isoSpec.inv ≫ p))
  have hSpec := smoothField_spectral_artinian_ideal K (X.isoSpec.inv ≫ p) i.appTop
    (i.app_surjective ⊤ (isAffineOpen_top X))
  have := idealPullbackMap_isIso_of_iso_square
    (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom (Scheme.isoSpec_hom_naturality i)
  exact isLocallyRankOne_of_iso X (asIso (idealPullbackMap
    (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom (Scheme.isoSpec_hom_naturality i)))
      (pullback_locallyRankOne X.isoSpec.hom _ hSpec)

/-- Every locally Artinian closed subscheme of a smooth field curve has
invertible actual ideal, including nonreduced and empty subschemes. -/
theorem smoothField_artinian_ideal
    (K : Type u) [Field K] [IsLocallyArtinian D]
    (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (i : D ⟶ X) [IsClosedImmersion i] :
    IsLocallyRankOne X (idealModule i) := by
  apply isLocallyRankOne_of_cover_restrict (idealModule i)
    (fun U : X.affineOpens ↦ U.val) (iSup_affineOpens_eq_top X)
  intro U
  let : IsAffine U.val.toScheme := U.property
  let : SmoothOfRelativeDimension 1 (U.val.ι ≫ p) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.val.ι ≫ p))
  exact isLocallyRankOne_of_iso U.val.toScheme (idealRestrictionIso i U.val).symm
    (smoothField_affine_artinian_ideal K (U.val.ι ≫ p) (i ∣_ U.val))

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

/-- The field-fibre input to Stacks Lemma 44.3.1 (0B9D), implication (3) to (2):
a finite closed subscheme of any smooth field curve has invertible actual kernel ideal.
The argument includes disconnected curves, arbitrary fields, and nonreduced or empty divisors. -/
theorem smoothFieldFiniteIdeal_isLocallyRankOne
    (K : Type u) [Field K] {X D : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (i : D ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ p)] :
    IsLocallyRankOne X (idealModule i) := by
  let : IsLocallyArtinian D := IsLocallyArtinian.of_locallyQuasiFinite (i ≫ p)
  exact smoothField_artinian_ideal K p i

/-- A principal ideal defining an Artinian quotient of a smooth affine field
curve is generated by a regular element. The curve need not be integral. -/
theorem smoothField_artinian_principalQuotient_isSMulRegular
    (K : Type u) [Field K] (R : CommRingCat.{u})
    (p : Spec R ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (a : R) [IsArtinianRing (R ⧸ Ideal.span {a})] : IsSMulRegular R a := by
  exact _root_.RingHom.artinianPrincipalKernel_isSMulRegular
    (Ideal.Quotient.mk (Ideal.span {a})) Ideal.Quotient.mk_surjective a Ideal.mk_ker
    (smoothField_maximal_localization_regular_dimension_one K R p)

/-- Version for the actual affine quotient map, avoiding a separate quotient-ring
presentation in the consumer. -/
theorem smoothField_artinian_principalKernel_isSMulRegular
    (K : Type u) [Field K] {R S : CommRingCat.{u}}
    (p : Spec R ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (φ : R ⟶ S) (hsurj : Function.Surjective φ.hom) [IsArtinianRing S]
    (a : R) (hker : RingHom.ker φ.hom = Ideal.span {a}) : IsSMulRegular R a := by
  exact _root_.RingHom.artinianPrincipalKernel_isSMulRegular φ.hom hsurj a hker
    (smoothField_maximal_localization_regular_dimension_one K R p)

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped nonZeroDivisors
variable {D X : Scheme.{u}} (i : D ⟶ X)

/-- The actual closed subscheme cut out by an invertible ideal in a smooth field curve
is locally Artinian, without properness or a reducedness hypothesis on the divisor. -/
theorem smoothFieldCartier_isLocallyArtinian
    (K : Type u) [Field K] {X D : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 p] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) : IsLocallyArtinian D := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hdim : topologicalKrullDim X ≤ 1 := by
    rw [topologicalKrullDim_eq_iSup_stalk]
    exact iSup_le (smoothOfRelativeDimension_stalk_dimension_le K X p 1)
  have hlocal (x : D) : ∃ U : X.Opens, IsAffineOpen U ∧ i x ∈ U ∧
      IsArtinianRing Γ(D, i ⁻¹ᵁ U) := by
    obtain ⟨U, hU, hxU, a, ha, hker⟩ :=
      exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI (i x)
    have hdimU : ringKrullDim Γ(X, U) ≤ 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      change topologicalKrullDim (Spec Γ(X, U)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le X U).trans hdim
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨U, hU, hxU,
      _root_.RingHom.quotient_isArtinianRing_of_regular_kernel_element (i.app U).hom
        (i.app_surjective U hU) hdimU a ha
        (RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self a))⟩
  choose U hU hxU hArt using hlocal
  have hcover : IsOpenCover (fun x : D ↦ i ⁻¹ᵁ U x) := .mk (by
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩)
  exact (isLocallyArtinian_iff_of_isOpenCover hcover (fun x ↦ (hU x).preimage i)).mpr hArt

end AlgebraicGeometry.Scheme.Hom
end
