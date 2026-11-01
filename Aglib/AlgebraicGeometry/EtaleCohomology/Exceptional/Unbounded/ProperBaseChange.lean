/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePlusComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CohomologicalBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.MateCubeIsomorphism
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Exchange

/-!
# Original unbounded proper exchange under two explicit relative bounds

For a torsion coefficient ring, the actual unbounded exchange is invertible
when both original direct images have supplied all-object finite cohomological
bounds. The proof supplies the original bounded-below proper theorem and actual
plus/full mate equation to the generic finite-amplitude exchange theorem.
Auxiliary abelian derived categories are chosen once inside the torsion-bound
bridge; the four public module derived categories remain independently sized. A separate corollary
transfers two supplied torsion-abelian bounds through the original underlying
comparison. No general geometric bound or non-quasi-compact localization is
asserted, and no absolute cohomological dimension of the base is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u wMX wMS wMX' wMS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include hN hΛ sq

/-- On every bounded-below object the same unbounded exchange is invertible,
by the original bounded-below proper map and the actual mate comparison. -/
theorem properModuleUnboundedDerivedBaseChange_isIso_of_isGE
    (K : DerivedCategory (ModuleSheaf X Λ)) (m : ℤ) [K.IsGE m] :
    IsIso ((moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  let P : DerivedCategory.Plus (ModuleSheaf X Λ) := ⟨K, ⟨m, inferInstance⟩⟩
  have hP : moduleTorsionCohomologyPlus X Λ P :=
    moduleTorsionCohomology_of_nsmul_one_eq_zero X Λ N hN hΛ K
  let : IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app P) :=
    properModuleDerivedBaseChange_isIso_of_torsion_homology Λ f f' g g' sq P hP
  have hc : HorizontalMateCubeEquation
      (moduleDerivedDirectImageCompιIso Λ f).hom
      (moduleDerivedDirectImageCompιIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (moduleDerivedInverseImageCompιIso Λ g).inv
      (moduleDerivedInverseImageCompιIso Λ g').inv :=
    moduleUnboundedDerivedBaseChangeMap_plus Λ f f' g g' sq.w.symm
  exact hc.isIso_target_app P

/-- The actual original unbounded proper exchange is an isomorphism under
explicit all-object bounds for both direct images. -/
theorem properModuleUnboundedDerivedBaseChange_isIso_of_bounds
    (d d' : ℕ)
    (hf : ∀ M : ModuleSheaf X Λ,
      IsZero (((moduleDirectImage f Λ).rightDerived (d + 1)).obj M))
    (hf' : ∀ M : ModuleSheaf X' Λ,
      IsZero (((moduleDirectImage f' Λ).rightDerived (d' + 1)).obj M)) :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  apply Functor.isIso_unboundedRightDerivedExchange_of_bounds
    (moduleDirectImage f Λ) (moduleDirectImage f' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage g' Λ)
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) d d' hf hf'
  intro K m hK
  let : K.IsGE m := hK
  exact properModuleUnboundedDerivedBaseChange_isIso_of_isGE Λ f f' g g' sq N hN hΛ K m

/-- Two supplied relative torsion-abelian bounds imply invertibility of the
same unbounded exchange through the actual coefficient-forgetting bridge. -/
theorem properModuleUnboundedDerivedBaseChange_isIso_of_torsion_bounds
    (d d' : ℕ)
    (hf : ∀ F : AbelianSheaf.{u, u + 1} X, Sheaf.IsTorsion F →
      IsZero ((higherDirectImage f (d + 1)).obj F))
    (hf' : ∀ F : AbelianSheaf.{u, u + 1} X', Sheaf.IsTorsion F →
      IsZero ((higherDirectImage f' (d' + 1)).obj F)) :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  exact properModuleUnboundedDerivedBaseChange_isIso_of_bounds Λ f f' g g' sq N hN hΛ d d'
    (moduleRightDerived_bound_of_torsion_bound Λ f N hN hΛ d hf)
    (moduleRightDerived_bound_of_torsion_bound Λ f' N hN hΛ d' hf')

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
