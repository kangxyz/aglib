/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleFullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.AbelianShortExact

/-! # The actual native module localization arrows and their zero composite -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]

/-- Outside the open, the original underlying native module extension stalk is zero. -/
theorem isZero_moduleLowerShriek_underlying_stalk_of_no_lift
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (hη : ∀ ζ : Spec (.of Ω) ⟶ U, ζ ≫ j ≠ η) (M : ModuleSheaf U Λ) :
    IsZero ((pointSmallEtale η).sheafFiber.obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj ((moduleLowerShriek j Λ).obj M))) := by
  have hz := isZero_etaleLowerShriek_stalk_of_no_lift j η hη
    ((SheafOfModules.toSheaf (constantRing U Λ)).obj M)
  exact hz.of_iso ((pointSmallEtale η).sheafFiber.mapIso
    ((moduleLowerShriekUnderlyingIso j Λ).app M))

/-- The original native module counit is invertible on every geometric stalk in the open. -/
theorem moduleLowerShriek_counit_underlying_stalk_isIso
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ U)
    (M : ModuleSheaf X Λ) :
    IsIso ((pointSmallEtale (ζ ≫ j)).sheafFiber.map
      ((SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleLowerShriekAdjunction j Λ).counit.app M))) := by
  let ε := (moduleLowerShriekAdjunction j Λ).counit.app M
  have : IsIso (((moduleInverseImage j Λ) ⋙
      SheafOfModules.toSheaf (constantRing U Λ)).map ε) := by
    change IsIso ((SheafOfModules.toSheaf (constantRing U Λ)).map
      ((moduleInverseImage j Λ).map ε))
    infer_instance
  have h := (NatIso.isIso_map_iff (moduleInverseImageUnderlyingIso Λ j) ε).mp this
  have : IsIso ((inverseImage j).map
      ((SheafOfModules.toSheaf (constantRing X Λ)).map ε)) := h
  apply (NatIso.isIso_map_iff (StalkInverseImage.nativeStalkIso j ζ) _).mpr
  change IsIso ((pointSmallEtale ζ).sheafFiber.map ((inverseImage j).map
    ((SheafOfModules.toSheaf (constantRing X Λ)).map ε)))
  infer_instance

variable (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)

include hcomp

/-- The original native module open counit followed by the original closed unit is zero. -/
@[reassoc]
theorem moduleLocalization_counit_comp_unit (M : ModuleSheaf X Λ) :
    (moduleLowerShriekAdjunction j Λ).counit.app M ≫
      (moduleInverseImageAdjunction i Λ).unit.app M = 0 := by
  classical
  apply (SheafOfModules.toSheaf (constantRing X Λ)).map_injective
  have (x : FibrewiseClosed.Index (𝟙 X)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply (StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 X)).jointlyFaithful.map_injective
  intro x
  let η := FibrewiseClosed.geometricPoint x.val
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
  by_cases hi : η default ∈ Set.range i
  · have hz := isZero_moduleLowerShriek_underlying_stalk_of_no_lift j Λ η
      (fun ζ hζ => by
        have hj : η default ∈ Set.range j :=
          ⟨ζ default, congrArg (fun f : _ ⟶ X => f default) hζ⟩
        rw [hcomp] at hj
        exact hj hi) ((moduleInverseImage j Λ).obj M)
    exact hz.eq_zero_of_src _
  · have hz := isZero_closedDirectImage_stalk_of_no_lift i η
      (fun ζ hζ => hi ⟨ζ default, congrArg (fun f : _ ⟶ X => f default) hζ⟩)
      ((SheafOfModules.toSheaf (constantRing Z Λ)).obj
        ((moduleInverseImage i Λ).obj M))
    exact hz.eq_zero_of_tgt _

/-- The literal native module localization short complex, without any exactness assumption. -/
def moduleLocalizationShortComplex (M : ModuleSheaf X Λ) : ShortComplex (ModuleSheaf X Λ) :=
  ShortComplex.mk ((moduleLowerShriekAdjunction j Λ).counit.app M)
    ((moduleInverseImageAdjunction i Λ).unit.app M)
    (moduleLocalization_counit_comp_unit j Λ i hcomp M)

end AlgebraicGeometry.Scheme.EtaleCohomology
