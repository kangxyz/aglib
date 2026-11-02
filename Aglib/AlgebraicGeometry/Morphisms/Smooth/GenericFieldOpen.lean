/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Dominant.Spec
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Stability

/-! # Smooth relative dimension on an actual generic open

The original dominant field point, literal restriction comparison, and complete
proper-model smooth spreading proof live here. The wide spreading-out module
reexports this unique implementation; no curve compactification, projectivity,
coherent cohomology or connected-component model is used by this construction.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The literal pullback of the restricted family is the literal pullback of
the original family whenever the chosen base map factors through the open. -/
def morphismRestrictBaseChangeIso {X Y T : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (g : T ⟶ Y) (gU : T ⟶ U) (hg : gU ≫ U.ι = g) :
    (Over.pullback gU).obj (Over.mk (f ∣_ U)) ≅
      (Over.pullback g).obj (Over.mk f) := by
  have h : IsPullback (pullback.fst (f ∣_ U) gU ≫ (f ⁻¹ᵁ U).ι)
      (pullback.snd (f ∣_ U) gU) f g := by
    simpa only [hg] using
      (IsPullback.of_hasPullback (f ∣_ U) gU).paste_horiz
        (isPullback_morphismRestrict f U).flip
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- The comparison keeps the original map to the total space. -/
@[reassoc]
theorem morphismRestrictBaseChangeIso_hom_fst {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (g : T ⟶ Y) (gU : T ⟶ U) (hg : gU ≫ U.ι = g) :
    (morphismRestrictBaseChangeIso f U g gU hg).hom.left ≫ pullback.fst f g =
      pullback.fst (f ∣_ U) gU ≫ (f ⁻¹ᵁ U).ι := by
  exact IsPullback.isoPullback_hom_fst _

/-- A dominant point with a one-point source is the actual generic point. -/
theorem dominant_subsingleton_apply_eq_genericPoint {T Y : Scheme.{u}}
    [Subsingleton T] [IrreducibleSpace Y] (g : T ⟶ Y) [IsDominant g] (x : T) :
    g x = genericPoint Y := by
  have hrange : Set.range g = {g x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg g (Subsingleton.elim z x)
    · rintro rfl
      exact ⟨x, rfl⟩
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  change closure ({g x} : Set Y) = Set.univ
  rw [← hrange]
  exact g.denseRange.closure_range

/-- A specified dominant field point factors through every open neighbourhood
of the actual generic point. -/
def liftDominantFieldPoint {Y : Scheme.{u}} [IrreducibleSpace Y]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) [IsDominant g]
    (U : Y.Opens) (hU : genericPoint Y ∈ U) : Spec (CommRingCat.of K) ⟶ U :=
  IsOpenImmersion.lift U.ι g (by
    rintro y ⟨x, rfl⟩
    rw [Opens.range_ι]
    exact (dominant_subsingleton_apply_eq_genericPoint g x).symm ▸ hU)

@[reassoc (attr := simp)]
theorem liftDominantFieldPoint_ι {Y : Scheme.{u}} [IrreducibleSpace Y]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) [IsDominant g]
    (U : Y.Opens) (hU : genericPoint Y ∈ U) : liftDominantFieldPoint g U hU ≫ U.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- Shrinking along a generic open preserves the supplied original-field
model comparison, as an isomorphism over that same original field. -/
def restrictModelComparison {X Y : Scheme.{u}} [IrreducibleSpace Y]
    {K : Type u} [Field K] (f : X ⟶ Y)
    (g : Spec (CommRingCat.of K) ⟶ Y) [IsDominant g]
    (C : Over (Spec (CommRingCat.of K)))
    (e : (Over.pullback g).obj (Over.mk f) ≅ C)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    (Over.pullback (liftDominantFieldPoint g U hU)).obj (Over.mk (f ∣_ U)) ≅ C :=
  morphismRestrictBaseChangeIso f U g (liftDominantFieldPoint g U hU)
    (liftDominantFieldPoint_ι g U hU) ≪≫ e

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- An actual proper finitely presented model over an integral affine base
can be shrunk to the relative dimension of its specified smooth field fibre.
The field embedding need not be algebraic over the fraction field. -/
theorem exists_generic_open_smoothOfRelativeDimension_of_fieldBaseChange
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [FaithfulSMul R K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (n : ℕ)
    [SmoothOfRelativeDimension n
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    ∃ U : (Spec (.of R)).Opens, genericPoint (Spec (.of R)) ∈ U ∧
      U ≠ ⊥ ∧ SmoothOfRelativeDimension n (f ∣_ U) := by
  let F := FractionRing R
  let : Algebra F K := FractionRing.liftAlgebra R K
  let : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  let gF := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let gK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let t := Spec.map (CommRingCat.ofHom (algebraMap F K))
  have ht : t ≫ gF = gK := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    exact (IsScalarTower.algebraMap_apply R F K r).symm
  let qF := pullback.snd f gF
  let qK := pullback.snd f gK
  let E := pullbackLeftPullbackSndIso f gF t ≪≫ pullback.congrHom rfl ht
  have hE : E.hom ≫ qK = pullback.snd qF t := by
    simp [E, qF, qK, Category.assoc]
  let : SmoothOfRelativeDimension n qK :=
    inferInstanceAs (SmoothOfRelativeDimension n
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
  let : Smooth qK := SmoothOfRelativeDimension.smooth n qK
  let : Smooth (pullback.snd qF t) := by
    rw [← hE]
    infer_instance
  let : Surjective t := ⟨Function.surjective_to_subsingleton t⟩
  let : Flat t := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : Smooth qF := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := qF) (g := t)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  let : Flat gF := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : IsPreimmersion gF := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let s := gF (Nonempty.some (inferInstance : Nonempty (Spec (.of F))))
  obtain ⟨U, hs, hsm⟩ := exists_open_smooth_of_isProper_of_flat_preimmersion f gF s
    ⟨Nonempty.some (inferInstance : Nonempty (Spec (.of F))), rfl⟩
  have hη : genericPoint (Spec (.of R)) ∈ U :=
    (genericPoint_specializes s).mem_open U.isOpen hs
  let : Smooth (f ∣_ U) := hsm
  let : IsDominant gK := specMap_dominant_of_injective _
    (FaithfulSMul.algebraMap_injective R K)
  let gU := liftDominantFieldPoint gK U hη
  have hgU : gU ≫ U.ι = gK := liftDominantFieldPoint_ι gK U hη
  let : IsDominant (gU ≫ U.ι) := by
    rw [hgU]
    infer_instance
  let : IsDominant gU := IsDominant.of_comp_of_isOpenImmersion gU U.ι
  let EU := morphismRestrictBaseChangeIso f U gK gU hgU
  let : SmoothOfRelativeDimension n (pullback.snd (f ∣_ U) gU) := by
    have hEU : EU.hom.left ≫ qK = pullback.snd (f ∣_ U) gU := EU.hom.w
    rw [← hEU]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension n) EU.hom.left qK).mpr inferInstance
  exact ⟨U, hη, U.ne_bot_iff_nonempty.mpr ⟨s, hs⟩,
    smoothOfRelativeDimension_of_dominant_fieldBaseChange (f ∣_ U) gU n⟩

end AlgebraicGeometry.Scheme
