/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.OpenCounitStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# The original abelian open-closed localization short exact sequence

Both arrows are the actual adjunction counit and unit. Exactness is detected
by the existing conservative family of original geometric stalks, using
actual lifts on the closed and open parts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  (F : AbelianSheaf.{u, u + 1} X)

include hcomp

/-- Every original geometric stalk sees exactly one nonzero part of the localization sequence. -/
theorem localization_stalk_cases {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X) :
    (IsIso ((pointSmallEtale η).sheafFiber.map
        ((etaleLowerShriekAdjunction j).counit.app F)) ∧
      IsZero ((pointSmallEtale η).sheafFiber.obj
        ((directImage i).obj ((inverseImage i).obj F)))) ∨
    (IsZero ((pointSmallEtale η).sheafFiber.obj
        ((etaleLowerShriek j).obj ((inverseImage j).obj F))) ∧
      IsIso ((pointSmallEtale η).sheafFiber.map
        ((inverseImageAdjunction i).unit.app F))) := by
  classical
  by_cases hi : η (default : Spec (.of Ω)) ∈ Set.range i
  · right
    obtain ⟨ζ, hζ⟩ := exists_closedImmersion_pointLift i η hi
    refine ⟨isZero_etaleLowerShriek_stalk_of_no_lift j η ?_ _,
      closedDirectImage_unit_stalk_isIso i ζ η hζ F⟩
    intro ξ hξ
    have hj : η (default : Spec (.of Ω)) ∈ Set.range j := by
      refine ⟨ξ (default : Spec (.of Ω)), ?_⟩
      exact congrArg (fun f : Spec (.of Ω) ⟶ X => f default) hξ
    rw [hcomp] at hj
    exact hj hi
  · left
    have hj : η (default : Spec (.of Ω)) ∈ Set.range j := by
      rw [hcomp]
      exact hi
    obtain ⟨ζ, hζ⟩ := exists_openImmersion_pointLift j η hj
    refine ⟨etaleLowerShriek_counit_stalk_isIso j ζ η hζ F,
      isZero_closedDirectImage_stalk_of_no_lift i η ?_ _⟩
    intro ξ hξ
    apply hi
    refine ⟨ξ (default : Spec (.of Ω)), ?_⟩
    exact congrArg (fun f : Spec (.of Ω) ⟶ X => f default) hξ

/-- The actual open counit followed by the actual closed unit vanishes. -/
@[reassoc]
theorem localization_counit_comp_unit :
    (etaleLowerShriekAdjunction j).counit.app F ≫
      (inverseImageAdjunction i).unit.app F = 0 := by
  have (x : FibrewiseClosed.Index (𝟙 X)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply (StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 X)).jointlyFaithful.map_injective
  intro x
  rw [Functor.map_comp, Functor.map_zero]
  rcases localization_stalk_cases j i hcomp F
      (FibrewiseClosed.geometricPoint x.val) with ⟨_, h⟩ | ⟨h, _⟩
  · exact h.eq_zero_of_tgt _
  · exact h.eq_zero_of_src _

/-- The literal open-closed localization short complex. -/
def abelianLocalizationShortComplex : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  ShortComplex.mk ((etaleLowerShriekAdjunction j).counit.app F)
    ((inverseImageAdjunction i).unit.app F) (localization_counit_comp_unit j i hcomp F)

/-- The original localization arrows form a short exact sequence for every abelian sheaf. -/
theorem abelianLocalization_shortExact :
    (abelianLocalizationShortComplex j i hcomp F).ShortExact := by
  have (x : FibrewiseClosed.Index (𝟙 X)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply ((StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 X)).shortExact_iff _).mpr
  intro x
  let S := (abelianLocalizationShortComplex j i hcomp F).map
    ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber)
  change S.ShortExact
  rcases localization_stalk_cases j i hcomp F
      (FibrewiseClosed.geometricPoint x.val) with ⟨hf, hz⟩ | ⟨hz, hg⟩
  · have : IsIso S.f := hf
    have : Epi S.g := hz.epi _
    exact ⟨(S.exact_iff_epi (hz.eq_zero_of_tgt _)).mpr inferInstance⟩
  · have : IsIso S.g := hg
    have : Mono S.f := hz.mono _
    exact ⟨(S.exact_iff_mono (hz.eq_zero_of_src _)).mpr inferInstance⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
