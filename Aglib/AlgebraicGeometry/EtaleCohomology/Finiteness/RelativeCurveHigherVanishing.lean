/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Bounded
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsField
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldConservative
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange

/-! # Higher roots-of-unity images for proper relative curves

The original proper exchange and original geometric points transport the broad
absolute curve vanishing theorem. No smoothness, normality, section, connectedness,
or Noetherian hypothesis is imposed on the family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w

attribute [local instance] hasSheafifyLarge

private theorem isZero_of_field_sections
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
    (h : IsZero ((globalSections (Spec (.of Ω))).obj F)) : IsZero F := by
  have hi : IsIso ((globalSections (Spec (.of Ω))).map (0 : F ⟶ F)) := by
    rw [Functor.map_zero]
    exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨h, h⟩
  let := hi
  have hi' := isIso_of_field_globalSections Ω (0 : F ⟶ F)
  exact ((isIsoZero_iff_source_target_isZero _ _).mp hi').1

/-- Absolute broad-curve vanishing, as a zero statement for the SAME original
higher direct image over the separably closed field. The cohomology universe is
independent of the native sheaf-value universe. -/
theorem rootsHigherDirectImage_isZero_over_isSepClosed
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of Ω))
    [LocallyOfFiniteType p] [CompactSpace Y]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    (hdim : topologicalKrullDim Y ≤ 1)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : Ω))
    (hinv : IsUnit (n : Γ(Y, ⊤))) (q : ℕ) (hq : 2 < q) :
    IsZero ((higherDirectImage p q).obj (mu Y n)) := by
  let := Curves.roots_subsingleton_H_of_curve Ω Y p hdim n hn hunit hinv q hq
  have hs := (cohomologyToHigherSections_bijective_of_isSepClosed Ω p (mu Y n) q).surjective
  have hz : Subsingleton ((globalSections (Spec (.of Ω))).obj
      ((higherDirectImage p q).obj (mu Y n))) := by
    constructor
    intro a b
    obtain ⟨a', rfl⟩ := hs a
    obtain ⟨b', rfl⟩ := hs b
    exact congrArg (cohomologyToHigherSections p (mu Y n) q) (Subsingleton.elim a' b')
  exact isZero_of_field_sections Ω _ (AddCommGrpCat.isZero_iff_subsingleton.mpr hz)

private theorem isZero_of_original_field_pullbacks
    {S : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} S)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      IsZero ((inverseImage η).obj F)) : IsZero F := by
  have hi : IsIso (0 : F ⟶ F) := by
    apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 S)
    intro Ω _ _ η _
    have hz := (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map_isZero (h Ω η)
    have he := (StalkInverseImage.stalkUnitNatIso η (𝟙 (Spec (.of Ω)))).app F
    have hz' : IsZero ((pointSmallEtale η).sheafFiber.obj F) := by
      simpa only [Category.id_comp] using hz.of_iso he
    rw [Functor.map_zero]
    exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hz', hz'⟩
  exact ((isIsoZero_iff_source_target_isZero _ _).mp hi).1

/-- Proper relative curves have no original roots-of-unity higher images above
 degree two, for an invertible positive level. The dimension premise concerns
 the actual geometric fibres; their cohomology vanishing is constructed internally. -/
theorem rootsHigherDirectImage_isZero_of_relativeCurve
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤)))
    (q : ℕ) (hq : 2 < q) : IsZero ((higherDirectImage f q).obj (mu X n)) := by
  apply isZero_of_original_field_pullbacks
  intro Ω _ _ η
  let p := pullback.snd f η
  have : IsProper p := inferInstanceAs (IsProper (pullback.snd f η))
  let : CompactSpace (pullback f η : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace p
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pullback f η)) := HasExt.standard _
  have hΩ : IsUnit (n : Ω) := by
    simpa only [map_natCast] using
      (levelInvertible η n hinv).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
  have hX := levelInvertible f n hinv
  have hY := levelInvertible (pullback.fst f η) n hX
  have hz := rootsHigherDirectImage_isZero_over_isSepClosed Ω p
    (hdim Ω η) n hn hΩ hY q hq
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (pullback f η))
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
  let α := (higherBaseChangeMap f p η (pullback.fst f η)
    (IsPullback.of_hasPullback f η).w.symm q).app (mu X n)
  have hα : IsIso α := by
    simpa only [α, higherBaseChangeMapFromDerived_eq] using
      (Proper.properHigherBaseChange_isIso_of_killed f p η (pullback.fst f η)
        (IsPullback.of_hasPullback f η) n (Nat.ne_of_gt hn) (mu X n)
        (mu_killedBy X n) q)
  let := hα
  let e := asIso α ≪≫ (higherDirectImage p q).mapIso
    (rootsPullbackIso (pullback.fst f η) n hn hX)
  exact hz.of_iso e

end AlgebraicGeometry.Scheme.EtaleCohomology
