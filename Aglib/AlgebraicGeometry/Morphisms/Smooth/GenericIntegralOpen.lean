/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericFieldOpen
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothGenericIntegrality
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Smooth geometrically integral generic fibres on an actual base open

The original proper family is restricted to an actual generic open on which
it is smooth of the same relative dimension and geometrically integral.
The two principal factors and the original fraction-field comparisons are
constructed here from the generic fibre. No family-property certificate is added.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme

universe u

/-- Smooth generic geometric integrality spreads on the original proper family.
The geometric-integrality input is on its actual original fraction-field fibre;
all intermediate principal factors are constructed internally. -/
theorem exists_generic_open_smooth_geometricallyIntegral
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    [LocallyOfFinitePresentation f] (n : ℕ)
    [SmoothOfRelativeDimension n (pullback.snd f (Spec.algebraMap R K))]
    [GeometricallyIntegral (pullback.snd f (Spec.algebraMap R K))] :
    ∃ V : (Spec (.of R)).Opens, genericPoint (Spec (.of R)) ∈ V ∧
      SmoothOfRelativeDimension n (f ∣_ V) ∧ GeometricallyIntegral (f ∣_ V) := by
  classical
  obtain ⟨U, hηU, _, hsmU⟩ :=
    Scheme.exists_generic_open_smoothOfRelativeDimension_of_fieldBaseChange (K := K) f n
  obtain ⟨_, ⟨a, rfl⟩, hηa, haU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hηU
  have ha : a ≠ 0 := by
    intro h
    simp only [h, PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.mem_bot] at hηa
  let A := Localization.Away a
  have hpow : Submonoid.powers a ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  let : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hpow
  have haK : algebraMap R K a ≠ 0 := by
    intro h
    exact ha ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  let φ : A →+* K := IsLocalization.Away.lift a (isUnit_iff_ne_zero.mpr haK)
  let : Algebra A K := φ.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq a (isUnit_iff_ne_zero.mpr haK) x).symm
  let : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers a) A K
  let b := Spec.algebraMap R A
  let k := Spec.algebraMap A K
  have hkb : k ≫ b = Spec.algebraMap R K := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply R A K x).symm
  have hbrange : Set.range b ⊆ (U : Set (Spec (.of R))) := by
    change Set.range (PrimeSpectrum.comap (algebraMap R A)) ⊆ _
    rw [PrimeSpectrum.localization_away_comap_range A a]
    exact haU
  let bU : Spec (.of A) ⟶ U := IsOpenImmersion.lift U.ι b (by
    simpa only [Scheme.Opens.range_ι] using hbrange)
  have hbU : bU ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  let q := pullback.snd f b
  let E := Scheme.morphismRestrictBaseChangeIso f U b bU hbU
  let : IsIso E.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of A))).map E.hom))
  have hq : SmoothOfRelativeDimension n q := by
    have h := MorphismProperty.pullback_snd
      (P := @SmoothOfRelativeDimension n) (f ∣_ U) bU hsmU
    have hw : E.hom.left ≫ q = pullback.snd (f ∣_ U) bU := E.hom.w
    rw [← hw] at h
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension n) E.hom.left q).mp h
  let : SmoothOfRelativeDimension n q := hq
  let EF := pullbackLeftPullbackSndIso f b k ≪≫ pullback.congrHom rfl hkb
  have hEF : EF.hom ≫ pullback.snd f (Spec.algebraMap R K) = pullback.snd q k := by
    simp [EF, q, Category.assoc]
  let : GeometricallyIntegral (pullback.snd q k) := by
    rw [← hEF]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) EF.hom _).mpr inferInstance
  let Ω := AlgebraicClosure K
  obtain ⟨c, hc, hGI⟩ :=
    Scheme.exists_ne_zero_geometricallyIntegral_smooth_principal A K Ω q n
  let T := Localization.Away c
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hc))
  let d := Spec.algebraMap A T
  let h := d ≫ b
  let V := h.opensRange
  let z : Spec (.of T) := ⟨⊥, inferInstance⟩
  have hηV : genericPoint (Spec (.of R)) ∈ V :=
    (genericPoint_specializes (h z)).mem_open V.isOpen ⟨z, rfl⟩
  let E₂ := pullbackLeftPullbackSndIso f b d
  have hE₂ : E₂.hom ≫ pullback.snd f h = pullback.snd q d := by
    simp [E₂, h, q]
  have hsm : SmoothOfRelativeDimension n (pullback.snd f h) := by
    have hi := MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) q d hq
    rw [← hE₂] at hi
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension n) E₂.hom _).mp hi
  have hgeo : GeometricallyIntegral (pullback.snd f h) := by
    change GeometricallyIntegral (pullback.snd q d) at hGI
    rw [← hE₂] at hGI
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) E₂.hom _).mp hGI
  let e := h.isoOpensRange
  let E₃ := Scheme.morphismRestrictBaseChangeIso f V h e.hom h.isoOpensRange_hom_ι
  let : IsIso E₃.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of T))).map E₃.hom))
  have transfer (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      (hP : P (pullback.snd f h)) : P (f ∣_ V) := by
    have hw : E₃.hom.left ≫ pullback.snd f h = pullback.snd (f ∣_ V) e.hom := E₃.hom.w
    have hq' : P (pullback.snd (f ∣_ V) e.hom) := by
      rw [← hw]
      exact (MorphismProperty.cancel_left_of_respectsIso
        (P := P) E₃.hom.left _).mpr hP
    have hp : P (pullback.fst (f ∣_ V) e.hom ≫ (f ∣_ V)) := by
      rw [pullback.condition]
      exact (MorphismProperty.cancel_right_of_respectsIso
        (P := P) _ e.hom).mpr hq'
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := P) (pullback.fst (f ∣_ V) e.hom) _).mp hp
  exact ⟨V, hηV, transfer (@SmoothOfRelativeDimension n) hsm,
    transfer @GeometricallyIntegral hgeo⟩

end AlgebraicGeometry.Scheme
