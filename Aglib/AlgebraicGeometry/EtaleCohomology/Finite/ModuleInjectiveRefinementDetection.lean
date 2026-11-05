/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleInjectiveClassTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedSummandDetection

/-! # One genuine finite coefficient replacement detecting every target refinement

The actual module retraction supplies its actual inverse-image adjunct. The
canonical finite mate and finite-cohomology comparison identify the resulting
literal pullback/coefficient class with the original retract summand. Hence
zero of that class detects the original class. The coefficient replacement
is chosen once, before the target family or any of its refinements.

This does not produce vanishing upstairs and never discards a finite
coefficient change without its actual retract and original class equation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite
open Coefficients
universe u eY eY'
attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- The literal transformed pullback class is detected using the given genuine
module retract, without replacing it by an abstract injective class map. -/
theorem moduleRetract_finite_pullback_class_eq_zero
    {T' T Y' Y : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')]
    (f : T' ⟶ T) [IsFinite f] (f' : Y' ⟶ Y)
    (b : Y ⟶ T) (b' : Y' ⟶ T') (h : IsPullback b' f' f b)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf T Λ) (J : ModuleSheaf T' Λ)
    (r : Retract I ((moduleDirectImage f Λ).obj J))
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)) q)
    (hc : Sheaf.H.map
      (moduleClosedPullbackCoefficientMap f f' b b' h.w.symm Λ I J
        (((moduleInverseImageAdjunction f Λ).homEquiv I J).symm r.i)) q
      (cohomologyPullback f' _ q c) = 0) : c = 0 := by
  have hz := moduleClosedSummand_eq_zero f f' b b' h Λ I J
    (((moduleInverseImageAdjunction f Λ).homEquiv I J).symm r.i) q c hc
  rw [Equiv.apply_symm_apply] at hz
  have hinj := Sheaf.H.map_injective_of_retract
    ((r.map (SheafOfModules.toSheaf (constantRing T Λ))).map (inverseImage b)) q
  exact hinj (hz.trans (map_zero _).symm)

/-- Construct one genuine upstairs injective and its original coefficient
adjunct, valid for every later target family and every actual cartesian
refinement. No cohomological zero is used for this existence statement. -/
theorem exists_moduleInjective_finite_refinement_detector
    {T' T : Scheme.{u}} (f : T' ⟶ T) [IsFinite f] [Surjective f]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf T Λ) [Injective I] :
    ∃ J : ModuleSheaf T' Λ, Injective J ∧
      ∃ a : (moduleInverseImage f Λ).obj I ⟶ J,
        ∀ {Y Y' : Scheme.{u}}
          [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
          [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')]
          (f' : Y' ⟶ Y) (b : Y ⟶ T) (b' : Y' ⟶ T')
          (h : IsPullback b' f' f b) (q : ℕ)
          (c : Sheaf.H.{eY} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)) q),
          Sheaf.H.map (moduleClosedPullbackCoefficientMap f f' b b' h.w.symm
            Λ I J a) q (cohomologyPullback f' _ q c) = 0 → c = 0 := by
  obtain ⟨J, hJ, ⟨r⟩⟩ := exists_moduleInjective_directImage_retract f Λ I
  refine ⟨J, hJ, ((moduleInverseImageAdjunction f Λ).homEquiv I J).symm r.i, ?_⟩
  intro Y Y' hY hY' f' b b' h q c hc
  exact moduleRetract_finite_pullback_class_eq_zero f f' b b' h Λ I J r q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
