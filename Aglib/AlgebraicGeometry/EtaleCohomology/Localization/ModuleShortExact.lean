/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleOpenPart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleClosedUnit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# The genuine constant-ring module localization short exact sequence

The arrows are the original native lower-shriek counit and inverse-image unit.
The original geometric stalk family proves short exactness after additive
forgetting. Native finite-limit preservation and conservative forgetting then
reflect the actual kernel fork; faithfulness reflects the epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ) (M : ModuleSheaf X Λ)

/-- The actual native localization arrows form a short exact sequence after additive forgetting. -/
theorem moduleLocalization_underlying_shortExact :
    ((moduleLocalizationShortComplex j Λ i hcomp M).map
      (SheafOfModules.toSheaf (constantRing X Λ))).ShortExact := by
  classical
  have (x : FibrewiseClosed.Index (𝟙 X)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply ((StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 X)).shortExact_iff _).mpr
  intro x
  let η := FibrewiseClosed.geometricPoint x.val
  let S := ((moduleLocalizationShortComplex j Λ i hcomp M).map
    (SheafOfModules.toSheaf (constantRing X Λ))).map (pointSmallEtale η).sheafFiber
  change S.ShortExact
  by_cases hi : η default ∈ Set.range i
  · obtain ⟨ζ, hζ⟩ := exists_closedImmersion_pointLift i η hi
    have : IsIso S.g := moduleClosed_unit_underlying_stalk_isIso i Λ ζ η hζ M
    have hz := isZero_moduleLowerShriek_underlying_stalk_of_no_lift j Λ η
      (fun ξ hξ => by
        have hj : η default ∈ Set.range j :=
          ⟨ξ default, congrArg (fun f : _ ⟶ X => f default) hξ⟩
        rw [hcomp] at hj
        exact hj hi) ((moduleInverseImage j Λ).obj M)
    have : Mono S.f := hz.mono _
    exact ⟨(S.exact_iff_mono (hz.eq_zero_of_src _)).mpr inferInstance⟩
  · have hj : η default ∈ Set.range j := by rw [hcomp]; exact hi
    obtain ⟨ζ, hζ⟩ := exists_openImmersion_pointLift j η hj
    have : IsIso S.f := by
      change IsIso ((pointSmallEtale η).sheafFiber.map
        ((SheafOfModules.toSheaf (constantRing X Λ)).map
          ((moduleLowerShriekAdjunction j Λ).counit.app M)))
      rw [← hζ]
      exact moduleLowerShriek_counit_underlying_stalk_isIso j Λ ζ M
    have hz := isZero_closedDirectImage_stalk_of_no_lift i η
      (fun ξ hξ => hi ⟨ξ default, congrArg (fun f : _ ⟶ X => f default) hξ⟩)
      ((SheafOfModules.toSheaf (constantRing Z Λ)).obj
        ((moduleInverseImage i Λ).obj M))
    have : Epi S.g := hz.epi _
    exact ⟨(S.exact_iff_epi (hz.eq_zero_of_tgt _)).mpr inferInstance⟩

/-- Every genuine constant-ring module sheaf has the original native localization SES. -/
theorem moduleLocalization_shortExact :
    (moduleLocalizationShortComplex j Λ i hcomp M).ShortExact := by
  let S := moduleLocalizationShortComplex j Λ i hcomp M
  let Q := SheafOfModules.toSheaf (constantRing X Λ)
  have h : (S.map Q).ShortExact := moduleLocalization_underlying_shortExact j Λ i hcomp M
  let : ReflectsLimitsOfShape WalkingParallelPair Q :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects Q ((KernelFork.isLimitMapConeEquiv _ Q).symm h.fIsKernel)
  let : Mono (Q.map S.f) := h.mono_f
  let : Epi (Q.map S.g) := h.epi_g
  let : Mono S.f := Functor.mono_of_mono_map Q h.mono_f
  let : Epi S.g := Functor.epi_of_epi_map Q h.epi_g
  exact ⟨S.exact_of_f_is_kernel hk⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
