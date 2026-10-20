/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.Norm
public import Aglib.RingTheory.DiscreteValuationRing.FiniteNorm
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# The full affine local model of a finite dominant morphism

This module constructs the localization of the entire inverse image of an
affine neighborhood at a target point. The base algebra is the actual target
stalk; its fraction fields and their map are the scheme function fields and
`Divisors.Scheme.functionFieldMap`. These are realization components for the family
`NormDegree.FiniteMorphismNormOrder`, not assumptions carrying its conclusion.
-/

@[expose] public section




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme IsDiscreteValuationRing.FiniteNorm
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

universe u
variable {X Y : Scheme.{u}} [hX : IsIntegral X] [hY : IsIntegral Y]
variable (f : X ⟶ Y) [hDominant : IsDominant f] [hFinite : IsFinite f]
variable (U : Y.Opens) (hU : IsAffineOpen U)

instance preimage_nonempty [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [Scheme.map_genericPoint_of_isDominant X f]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using ‹Nonempty U›)

@[instance_reducible]
def chartAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

attribute [local instance] chartAlgebra

omit hFinite in
/-- Generic restriction commutes with pullback on the entire inverse-image chart. -/
theorem fieldMap_germ
    [IsFinite f]
    [Nonempty U] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (Scheme.functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.presheaf.germ U _ _ ≫
    (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap]

theorem chartMap_injective [Nonempty U] : Function.Injective (f.app U) := by
  intro a b hab
  apply Y.germToFunctionField_injective U
  apply (Scheme.functionFieldMap f).injective
  have h := congrArg (fun g : Γ(Y, U) ⟶ X.functionField => (g a, g b))
    (fieldMap_germ f U)
  exact (congrArg Prod.fst h).trans ((congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hab).trans
    (congrArg Prod.snd h).symm)

include hU in
omit hX hY hDominant in
theorem chart_finite
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU

variable (y : U)

/-- Denominators are all functions on the target chart not vanishing at `y`. -/
def denominators : Submonoid Γ(X, f ⁻¹ᵁ U) :=
  Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U) (hU.primeIdealOf y).asIdeal.primeCompl

/-- This localizes the full inverse-image chart, without selecting a source branch. -/
abbrev Ring := Localization (denominators f U hU y)

variable [hNonempty : Nonempty U]
local instance stalkChartAlgebra : Algebra Γ(Y, U) (Y.presheaf.stalk y.val) :=
  TopCat.Presheaf.algebra_section_stalk Y.presheaf y

local instance stalk_isLocalization :
    IsLocalization.AtPrime (Y.presheaf.stalk y.val) (hU.primeIdealOf y).asIdeal :=
  hU.isLocalization_stalk y

local instance model_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U)
      (hU.primeIdealOf y).asIdeal.primeCompl) (Ring f U hU y) := by
  change IsLocalization (denominators f U hU y) (Localization (denominators f U hU y))
  infer_instance

@[instance_reducible]
def stalkAlgebra : Algebra (Y.presheaf.stalk y.val) (Ring f U hU y) :=
  localizationAlgebra (hU.primeIdealOf y).asIdeal.primeCompl Γ(X, f ⁻¹ᵁ U)

attribute [local instance] stalkAlgebra

instance chart_stalk_scalarTower :
    IsScalarTower Γ(Y, U) (Y.presheaf.stalk y.val) (Ring f U hU y) :=
  isScalarTower_localizationAlgebra (Rₘ := Y.presheaf.stalk y.val)
    (Sₘ := Ring f U hU y) (hU.primeIdealOf y).asIdeal.primeCompl Γ(X, f ⁻¹ᵁ U)

/-- The full localized chart is finite over the actual target stalk. -/
instance finite : Module.Finite (Y.presheaf.stalk y.val) (Ring f U hU y) := by
  letI := chart_finite f U hU
  exact Module.Finite.of_isLocalization Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
    (hU.primeIdealOf y).asIdeal.primeCompl

theorem denominators_le_nonZeroDivisors :
    denominators f U hU y ≤ nonZeroDivisors Γ(X, f ⁻¹ᵁ U) := by
  rintro s ⟨r, hr, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  change f.app U r ≠ 0
  simpa using (chartMap_injective f U).ne (nonZeroDivisors.coe_ne_zero
    ⟨r, (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors hr⟩)

/-- Integrality is preserved because the localized chart embeds in its function field. -/
instance domain : IsDomain (Ring f U hU y) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (denominators_le_nonZeroDivisors f U hU y)

/-- The full local model maps to the actual source function field by generic restriction. -/
@[instance_reducible]
def functionFieldAlgebra : Algebra (Ring f U hU y) X.functionField :=
  (IsLocalization.lift (S := Ring f U hU y)
    (g := (X.germToFunctionField (f ⁻¹ᵁ U)).hom)
    (fun s : denominators f U hU y => isUnit_iff_ne_zero.mpr (by
      intro hs
      apply nonZeroDivisors.coe_ne_zero
        (⟨s.val, denominators_le_nonZeroDivisors f U hU y s.property⟩ :
          nonZeroDivisors Γ(X, f ⁻¹ᵁ U))
      apply X.germToFunctionField_injective (f ⁻¹ᵁ U)
      exact hs.trans (map_zero (X.germToFunctionField (f ⁻¹ᵁ U)).hom).symm))).toAlgebra

attribute [local instance] functionFieldAlgebra

instance source_chart_scalarTower :
    IsScalarTower Γ(X, f ⁻¹ᵁ U) (Ring f U hU y) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq
  intro s
  exact (IsLocalization.lift_eq (M := denominators f U hU y)
    (S := Ring f U hU y) (g := (X.germToFunctionField (f ⁻¹ᵁ U)).hom) _ s).symm

/-- The fractions of the full local model are the actual source function field. -/
instance isFractionRing : IsFractionRing (Ring f U hU y) X.functionField := by
  letI := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (denominators f U hU y) (Ring f U hU y) X.functionField

@[instance_reducible]
def stalkFieldAlgebra : Algebra (Y.presheaf.stalk y.val) X.functionField :=
  ((Scheme.functionFieldMap f).comp (algebraMap (Y.presheaf.stalk y.val) Y.functionField)).toAlgebra

omit hFinite hNonempty in
/-- The target-stalk map into the source field is exactly induced by `Scheme.functionFieldMap`. -/
theorem stalk_field_scalarTower
    [IsFinite f]
    [Nonempty U]
    :
    letI := Scheme.functionFieldMapAlgebra f
    letI := stalkFieldAlgebra f U y
    IsScalarTower (Y.presheaf.stalk y.val) Y.functionField X.functionField := by
  letI := Scheme.functionFieldMapAlgebra f
  letI := stalkFieldAlgebra f U y
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The full local model and the actual function-field pullback give the same target-stalk map. -/
theorem stalk_model_scalarTower :
    letI := stalkFieldAlgebra f U y
    IsScalarTower (Y.presheaf.stalk y.val) (Ring f U hU y) X.functionField := by
  letI := stalkFieldAlgebra f U y
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (hU.primeIdealOf y).asIdeal.primeCompl
  ext r
  change Scheme.functionFieldMap f
      (algebraMap (Y.presheaf.stalk y.val) Y.functionField
        (Y.presheaf.germ U y.val y.property r)) = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  rw [RingHom.comp_apply, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply Γ(Y, U) (Y.presheaf.stalk y.val) (Ring f U hU y),
    IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, f ⁻¹ᵁ U) (Ring f U hU y),
    ← IsScalarTower.algebraMap_apply Γ(X, f ⁻¹ᵁ U) (Ring f U hU y) X.functionField]
  exact congrArg (fun g : Γ(Y, U) ⟶ X.functionField => g r) (fieldMap_germ f U)

omit hX hY hDominant hFinite hNonempty in
/-- The local model is the entire affine base change by the actual target-stalk map. -/
theorem isPullback_affine
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    [IsFinite f]
    [Nonempty U]
    : CategoryTheory.IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, f ⁻¹ᵁ U) (Ring f U hU y))))
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y.val) (Ring f U hU y))))
    (Spec.map (f.app U)) (Spec.map (Y.presheaf.germ U y.val y.property)) := by
  apply isPullback_SpecMap_of_isPushout
  letI := Algebra.isPushout_of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
    (Y.presheaf.stalk y.val) Γ(X, f ⁻¹ᵁ U) (Ring f U hU y)
  exact CommRingCat.isPushout_of_isPushout Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
    (Y.presheaf.stalk y.val) (Ring f U hU y)

/-- `Spec` of the local model is the FULL inverse image over the target stalk. -/
theorem isPullback : CategoryTheory.IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, f ⁻¹ᵁ U) (Ring f U hU y))) ≫
      (hU.preimage f).fromSpec)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y.val) (Ring f U hU y))))
    f (Y.fromSpecStalk y.val) := by
  have hc : CategoryTheory.IsPullback (hU.preimage f).fromSpec
      (Spec.map (f.app U)) f hU.fromSpec := by
    apply CategoryTheory.IsPullback.flip
    apply IsOpenImmersion.isPullback
    · simpa only [Scheme.Hom.appLE_eq_app] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl).symm
    · rw [hU.opensRange_fromSpec, (hU.preimage f).opensRange_fromSpec]
  have h := (isPullback_affine f U hU y).paste_horiz hc
  change CategoryTheory.IsPullback _ _ f (hU.fromSpecStalk y.property) at h
  rwa [hU.fromSpecStalk_eq_fromSpecStalk] at h

/-- Canonical realization of the full finite inverse image over the actual target local scheme. -/
def schemeIso : Spec (.of (Ring f U hU y)) ≅
    CategoryTheory.Limits.pullback f (Y.fromSpecStalk y.val) :=
  (isPullback f U hU y).isoPullback

/-- The source-chart prime belonging to a maximal branch of the full local model. -/
def branchPrime (q : MaximalSpectrum (Ring f U hU y)) : PrimeSpectrum Γ(X, f ⁻¹ᵁ U) :=
  q.toPrimeSpectrum.comap (algebraMap Γ(X, f ⁻¹ᵁ U) (Ring f U hU y))

omit hNonempty in
theorem branchPrime_comap
    [Nonempty U]
    (q : MaximalSpectrum (Ring f U hU y)) :
    (branchPrime f U hU y q).comap (f.app U).hom = hU.primeIdealOf y := by
  letI : q.asIdeal.IsMaximal := q.isMaximal
  have hq : q.asIdeal.comap (algebraMap (Y.presheaf.stalk y.val) (Ring f U hU y)) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y.val) :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)
  rw [hU.primeIdealOf_eq_map_closedPoint y]
  apply PrimeSpectrum.ext
  ext r
  change algebraMap Γ(X, f ⁻¹ᵁ U) (Ring f U hU y) (f.app U r) ∈ q.asIdeal ↔ _
  change algebraMap Γ(X, f ⁻¹ᵁ U) (Ring f U hU y)
      (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) r) ∈ q.asIdeal ↔ _
  rw [← IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, f ⁻¹ᵁ U) (Ring f U hU y),
    IsScalarTower.algebraMap_apply Γ(Y, U) (Y.presheaf.stalk y.val) (Ring f U hU y)]
  change algebraMap Γ(Y, U) (Y.presheaf.stalk y.val) r ∈
    q.asIdeal.comap (algebraMap (Y.presheaf.stalk y.val) (Ring f U hU y)) ↔ _
  rw [hq]
  rfl

/-- The actual source point of a maximal branch. -/
def branchPoint (q : MaximalSpectrum (Ring f U hU y)) : X :=
  (hU.preimage f).fromSpec (branchPrime f U hU y q)

theorem branchPoint_map (q : MaximalSpectrum (Ring f U hU y)) :
    f (branchPoint f U hU y q) = y.val := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  have h' := congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => g (branchPrime f U hU y q)) h
  change hU.fromSpec ((branchPrime f U hU y q).comap (f.app U).hom) =
    f (branchPoint f U hU y q) at h'
  rw [branchPrime_comap, hU.fromSpec_primeIdealOf] at h'
  exact h'.symm

theorem branchPoint_closed (hy : IsClosed ({y.val} : Set Y))
    (q : MaximalSpectrum (Ring f U hU y)) : IsClosed ({branchPoint f U hU y q} : Set X) := by
  letI := (f.isDiscrete_preimage_singleton y.val).to_subtype
  let x : f ⁻¹' ({y.val} : Set Y) := ⟨branchPoint f U hU y q, branchPoint_map f U hU y q⟩
  simpa only [Set.image_singleton] using
    (hy.preimage f.continuous).isClosedMap_subtype_val ({x}) isClosed_singleton

omit hX hY hDominant hNonempty in
theorem branchPoint_injective
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    [Nonempty U]
    : Function.Injective (branchPoint f U hU y) := by
  intro q r h
  have hpr : branchPrime f U hU y q = branchPrime f U hU y r :=
    (hU.preimage f).fromSpec.isOpenEmbedding.injective h
  have he := PrimeSpectrum.localization_comap_injective (Ring f U hU y)
    (denominators f U hU y) hpr
  exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal he)

omit hX hY hDominant hNonempty in
/-- Every actual closed point above `y` gives a maximal branch; none is omitted. -/
theorem exists_branch
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    [Nonempty U]
    (x : X) (hx : IsClosed ({x} : Set X)) (hfx : f x = y.val) :
    ∃ q : MaximalSpectrum (Ring f U hU y), branchPoint f U hU y q = x := by
  have hxU : x ∈ f ⁻¹ᵁ U := by change f x ∈ U; rw [hfx]; exact y.property
  let p := (hU.preimage f).primeIdealOf ⟨x, hxU⟩
  have hp : p.comap (f.app U).hom = hU.primeIdealOf y := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U)
      (hU.preimage f) le_rfl hxU
    rw [Scheme.Hom.appLE_eq_app] at h
    convert h using 1
    exact congrArg hU.primeIdealOf (Subtype.ext hfx.symm)
  have hd : Disjoint (denominators f U hU y : Set Γ(X, f ⁻¹ᵁ U)) p.asIdeal := by
    rw [Set.disjoint_left]
    rintro s ⟨r, hr, rfl⟩ hs
    apply hr
    have hmem : r ∈ (p.comap (f.app U).hom).asIdeal := hs
    rwa [hp] at hmem
  letI : p.asIdeal.IsMaximal := (hU.preimage f).primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  have hm := IsLocalization.isMaximal_of_isMaximal_disjoint
    (denominators f U hU y) (Ring f U hU y) p.asIdeal hd
  let q : MaximalSpectrum (Ring f U hU y) := ⟨p.asIdeal.map (algebraMap _ _), hm⟩
  refine ⟨q, ?_⟩
  have hq : branchPrime f U hU y q = p := by
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint
      (denominators f U hU y) (Ring f U hU y) p.isPrime hd
  change (hU.preimage f).fromSpec (branchPrime f U hU y q) = x
  rw [hq]
  exact (hU.preimage f).fromSpec_primeIdealOf ⟨x, hxU⟩

section ClosedFibre
variable [hNoetherianX : AlgebraicGeometry.IsNoetherian X]
  [hNoetherianY : AlgebraicGeometry.IsNoetherian Y]

def branchClosedFibre (hy : IsClosed ({y.val} : Set Y))
    (q : MaximalSpectrum (Ring f U hU y)) : ClosedFibre f ⟨y.val, hy⟩ :=
  ⟨⟨branchPoint f U hU y q, branchPoint_closed f U hU y hy q⟩,
    Subtype.ext (branchPoint_map f U hU y q)⟩

/-- All maximal branches are in bijection with all actual closed fibre points. -/
def closedFibreEquiv (hy : IsClosed ({y.val} : Set Y)) :
    MaximalSpectrum (Ring f U hU y) ≃ ClosedFibre f ⟨y.val, hy⟩ :=
  Equiv.ofBijective (branchClosedFibre f U hU y hy) ⟨by
    intro q r h
    exact branchPoint_injective f U hU y (congrArg (fun x => x.val.val) h), by
    intro x
    obtain ⟨q, hq⟩ := exists_branch f U hU y x.val.val x.val.property
      (congrArg Subtype.val x.property)
    exact ⟨q, Subtype.ext (Subtype.ext hq)⟩⟩

end ClosedFibre

omit hX hY hDominant hNonempty in
/-- The branch point lies in the full inverse-image chart. -/
theorem branchPoint_mem
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    [Nonempty U]
    (q : MaximalSpectrum (Ring f U hU y)) :
    branchPoint f U hU y q ∈ f ⁻¹ᵁ U :=
  ((hU.preimage f).isoSpec.inv (branchPrime f U hU y q)).property

theorem primeIdealOf_branchPoint (q : MaximalSpectrum (Ring f U hU y)) :
    (hU.preimage f).primeIdealOf
      ⟨branchPoint f U hU y q, branchPoint_mem f U hU y q⟩ = branchPrime f U hU y q := by
  apply (hU.preimage f).fromSpec.isOpenEmbedding.injective
  rw [(hU.preimage f).fromSpec_primeIdealOf]
  rfl

@[instance_reducible]
def branchStalkAlgebra (q : MaximalSpectrum (Ring f U hU y)) :
    Algebra Γ(X, f ⁻¹ᵁ U) (X.presheaf.stalk (branchPoint f U hU y q)) :=
  TopCat.Presheaf.algebra_section_stalk X.presheaf
    ⟨branchPoint f U hU y q, branchPoint_mem f U hU y q⟩

attribute [local instance] branchStalkAlgebra

instance branchStalk_isLocalization (q : MaximalSpectrum (Ring f U hU y)) :
    IsLocalization.AtPrime (X.presheaf.stalk (branchPoint f U hU y q))
      (branchPrime f U hU y q).asIdeal := by
  rw [← primeIdealOf_branchPoint f U hU y q]
  exact (hU.preimage f).isLocalization_stalk
    ⟨branchPoint f U hU y q, branchPoint_mem f U hU y q⟩

/-- Each maximal localization is canonically the actual stalk at its fibre point. -/
instance branchLocalization_isLocalization (q : MaximalSpectrum (Ring f U hU y)) :
    IsLocalization.AtPrime (Localization.AtPrime q.asIdeal)
      (branchPrime f U hU y q).asIdeal := by
  change IsLocalization.AtPrime (Localization.AtPrime q.asIdeal)
    (q.asIdeal.comap (algebraMap Γ(X, f ⁻¹ᵁ U) (Ring f U hU y)))
  infer_instance

/-- Each maximal localization is canonically the actual stalk at its fibre point. -/
def branchStalkEquiv (q : MaximalSpectrum (Ring f U hU y)) :
    Localization.AtPrime q.asIdeal ≃ₐ[Γ(X, f ⁻¹ᵁ U)]
      X.presheaf.stalk (branchPoint f U hU y q) :=
  IsLocalization.algEquiv (branchPrime f U hU y q).asIdeal.primeCompl _ _

/-- Under this canonical equivalence, both stalks have the same generic restriction map. -/
theorem branchStalkEquiv_fraction (q : MaximalSpectrum (Ring f U hU y)) :
    letI := branchFractionAlgebra (L := X.functionField) q
    (algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) X.functionField).comp
      (branchStalkEquiv f U hU y q).toRingHom =
        algebraMap (Localization.AtPrime q.asIdeal) X.functionField := by
  letI := branchFractionAlgebra (L := X.functionField) q
  letI := branchFraction_scalarTower (L := X.functionField) q
  apply IsLocalization.ringHom_ext (branchPrime f U hU y q).asIdeal.primeCompl
  ext s
  simp only [RingHom.comp_apply]
  change algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) X.functionField
    (branchStalkEquiv f U hU y q (algebraMap Γ(X, f ⁻¹ᵁ U) (Localization.AtPrime q.asIdeal) s)) = _
  rw [AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply Γ(X, f ⁻¹ᵁ U) (Ring f U hU y)
      (Localization.AtPrime q.asIdeal),
    ← IsScalarTower.algebraMap_apply (Ring f U hU y) (Localization.AtPrime q.asIdeal)
      X.functionField,
    ← IsScalarTower.algebraMap_apply Γ(X, f ⁻¹ᵁ U) (Ring f U hU y) X.functionField]
  exact Scheme.algebraMap_germ_eq_germToFunctionField X (branchPoint_mem f U hU y q) s

theorem branch_isDiscreteValuationRing
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (hy : IsClosed ({y.val} : Set Y)) (q : MaximalSpectrum (Ring f U hU y)) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let x : ClosedPoint X := ⟨branchPoint f U hU y q, branchPoint_closed f U hU y hy q⟩
  letI : IsDiscreteValuationRing (X.presheaf.stalk (branchPoint f U hU y q)) :=
    inferInstanceAs (IsDiscreteValuationRing (X.presheaf.stalk x.val))
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (branchStalkEquiv f U hU y q).symm

/-- The actual stalk map with its target point transported along an explicit fibre equality. -/
def stalkMapAt (x : X) (v : Y) (hx : f x = v) :
    Y.presheaf.stalk v →+* X.presheaf.stalk x :=
  ((Y.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ f.stalkMap x).hom

instance stalkMapAt_isLocalHom (x : X) (v : Y) (hx : f x = v) :
    IsLocalHom (stalkMapAt f x v hx) := by
  subst v
  simpa [stalkMapAt] using (inferInstance : IsLocalHom (f.stalkMap x).hom)

omit hX hY hDominant hFinite hNonempty in
theorem stalkMapAt_germ
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    [IsFinite f]
    [Nonempty U]
    (x : X) (v : Y) (hx : f x = v) (hv : v ∈ U)
    (hxU : x ∈ f ⁻¹ᵁ U) (r : Γ(Y, U)) :
    stalkMapAt f x v hx (Y.presheaf.germ U v hv r) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hxU (f.app U r) := by
  subst v
  simp [stalkMapAt]

/-- The localization/stalk equivalence intertwines the actual morphism on local rings. -/
theorem branchStalkEquiv_stalkMap (q : MaximalSpectrum (Ring f U hU y)) :
    (branchStalkEquiv f U hU y q).toRingHom.comp
      (algebraMap (Y.presheaf.stalk y.val) (Localization.AtPrime q.asIdeal)) =
    stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) := by
  apply IsLocalization.ringHom_ext (hU.primeIdealOf y).asIdeal.primeCompl
  ext r
  simp only [RingHom.comp_apply]
  change branchStalkEquiv f U hU y q
      (algebraMap (Y.presheaf.stalk y.val) (Localization.AtPrime q.asIdeal)
        (algebraMap Γ(Y, U) (Y.presheaf.stalk y.val) r)) = _
  rw [IsScalarTower.algebraMap_apply (Y.presheaf.stalk y.val) (Ring f U hU y)
      (Localization.AtPrime q.asIdeal),
    ← IsScalarTower.algebraMap_apply Γ(Y, U) (Y.presheaf.stalk y.val) (Ring f U hU y),
    IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, f ⁻¹ᵁ U) (Ring f U hU y),
    ← IsScalarTower.algebraMap_apply Γ(X, f ⁻¹ᵁ U) (Ring f U hU y)
      (Localization.AtPrime q.asIdeal), AlgEquiv.commutes]
  exact (stalkMapAt_germ f U (branchPoint f U hU y q) y.val
    (branchPoint_map f U hU y q) y.property (branchPoint_mem f U hU y q) r).symm

local instance branch_isLocalHom (q : MaximalSpectrum (Ring f U hU y)) :
    IsLocalHom (algebraMap (Y.presheaf.stalk y.val) (Localization.AtPrime q.asIdeal)) :=
  localizationAtMaximal_isLocalHom q.asIdeal

/-- The actual residue-field isomorphism induced by the canonical stalk identification. -/
def branchResidueEquiv (q : MaximalSpectrum (Ring f U hU y)) :
    IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal) ≃+*
      X.residueField (branchPoint f U hU y q) :=
  IsLocalRing.ResidueField.mapEquiv (branchStalkEquiv f U hU y q).toRingEquiv

section ResidueDegree
variable [hNoetherianX : AlgebraicGeometry.IsNoetherian X]
  [hNoetherianY : AlgebraicGeometry.IsNoetherian Y]

omit hNoetherianX hNoetherianY in
/-- The residue degrees in the algebraic norm formula are the actual geometric residue degrees. -/
theorem branch_residueDegree
    [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y]
    (hy : IsClosed ({y.val} : Set Y))
    (q : MaximalSpectrum (Ring f U hU y)) :
    (Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk y.val))
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ) =
    residueDegreeInt f (branchClosedFibre f U hU y hy q).val := by
  let x : ClosedPoint X := (branchClosedFibre f U hU y hy q).val
  letI := relativeResidueAlgebra f x
  let i : IsLocalRing.ResidueField (Y.presheaf.stalk y.val) ≃+* Y.residueField (f x.val) :=
    IsLocalRing.ResidueField.mapEquiv
      (Y.presheaf.stalkCongr (.of_eq (branchPoint_map f U hU y q).symm)).commRingCatIsoToRingEquiv
  let j : IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal) ≃+* X.residueField x.val :=
    branchResidueEquiv f U hU y q
  have hc : (algebraMap (Y.residueField (f x.val)) (X.residueField x.val)).comp i.toRingHom =
      j.toRingHom.comp (algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk y.val))
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))) := by
    ext a
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := Y.presheaf.stalk y.val) a
    change IsLocalRing.residue (X.presheaf.stalk x.val)
        (stalkMapAt f x.val y.val (branchPoint_map f U hU y q) r) =
      IsLocalRing.residue (X.presheaf.stalk x.val)
        (branchStalkEquiv f U hU y q
          (algebraMap (Y.presheaf.stalk y.val) (Localization.AtPrime q.asIdeal) r))
    exact congrArg (IsLocalRing.residue (X.presheaf.stalk x.val))
      (congrArg (fun g : Y.presheaf.stalk y.val →+* X.presheaf.stalk x.val => g r)
        (branchStalkEquiv_stalkMap f U hU y q)).symm
  change (Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk y.val))
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ) =
    (Module.finrank (Y.residueField (f x.val)) (X.residueField x.val) : ℤ)
  exact_mod_cast Algebra.finrank_eq_of_equiv_equiv i j hc

end ResidueDegree

variable [IsDiscreteValuationRing (Y.presheaf.stalk y.val)]

/-- The full local model is free over the actual target DVR. -/
instance free : Module.Free (Y.presheaf.stalk y.val) (Ring f U hU y) := by
  letI := Scheme.functionFieldMapAlgebra f
  letI := stalkFieldAlgebra f U y
  letI := stalk_field_scalarTower f U y
  letI := stalk_model_scalarTower f U hU y
  exact finiteDomain_free (A := Y.presheaf.stalk y.val) (B := Ring f U hU y)
    (K := Y.functionField) (L := X.functionField)

/-- All maximal branches of the full local model form a finite set. -/
instance maximal_finite : Finite (MaximalSpectrum (Ring f U hU y)) :=
  maximalSpectrum_finite_of_finite_algebra (A := Y.presheaf.stalk y.val)

/-- Determinant norm of the full local model agrees with the prescribed geometric field norm. -/
theorem fieldNorm_algebraMap (b : Ring f U hU y) :
    fieldNorm f (algebraMap (Ring f U hU y) X.functionField b) =
      algebraMap (Y.presheaf.stalk y.val) Y.functionField
        (Algebra.norm (Y.presheaf.stalk y.val) b) := by
  letI := Scheme.functionFieldMapAlgebra f
  letI := stalkFieldAlgebra f U y
  letI := stalk_field_scalarTower f U y
  letI := stalk_model_scalarTower f U hU y
  exact IsDiscreteValuationRing.FiniteNorm.fieldNorm_algebraMap (A := Y.presheaf.stalk y.val)
    (B := Ring f U hU y) (K := Y.functionField) (L := X.functionField) b

end AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Finite/LocalNormAlgebra.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 00f2f0b8d7d6f9bc44b71def80226ffd1a9c6299e8d8ed7097b58c24aff1684a.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
