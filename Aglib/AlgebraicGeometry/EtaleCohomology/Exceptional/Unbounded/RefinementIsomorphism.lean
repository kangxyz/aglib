/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementComparison
public import Aglib.CategoryTheory.Adjunction.Mates.UnitIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperBaseChangeTheorem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenClosedDetection
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Invertibility of the original compactification-refinement comparison

Proper base change and the original mate-unit equation show that the original
unit is invertible on an open extension: on the open part its base change is
the unit of the identity, and on the complementary closed part its source is
zero. Joint open/closed detection then applies to this same unit. Composing
with the previously constructed open pullback isomorphism proves invertibility
of the unchanged refinement comparison, on every unbounded object over a torsion ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients


universe u w w₁ w₂ wZ

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf D.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ

private theorem refinementUnit_open_isIso
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedInverseImage Λ D.j).map
      ((moduleUnboundedDerivedAdjunction Λ a.hom).unit.app
        ((moduleUnboundedDerivedLowerShriek D.j Λ).obj K))) := by
  let E := (moduleUnboundedDerivedLowerShriek D.j Λ).obj K
  let sq := Hom.DenseCompactification.isPullback_open a
  have hbc : IsIso ((moduleUnboundedDerivedBaseChangeMap Λ a.hom (𝟙 X) D.j C.j sq.w.symm).app
      ((moduleUnboundedDerivedInverseImage Λ a.hom).obj E)) := by
    let := Proper.properModuleUnboundedDerivedBaseChange_isIso
      Λ a.hom (𝟙 X) D.j C.j sq N hN hΛ
    infer_instance
  let : (moduleUnboundedDerivedInverseImage Λ (𝟙 X)).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleUnboundedDerivedInverseImageIdIso Λ X).symm
  exact isIso_map_unit_of_iso_mate (moduleUnboundedDerivedAdjunction Λ a.hom)
    (moduleUnboundedDerivedAdjunction Λ (𝟙 X))
    (moduleUnboundedDerivedInverseImageSquareIso Λ a.hom (𝟙 X) D.j C.j sq.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ a.hom (𝟙 X) D.j C.j sq.w.symm)
    rfl E hbc inferInstance

omit [QuasiCompact f] in
private theorem refinementUnit_closed_isIso
    {Z : Scheme.{u}} (i : Z ⟶ D.Xbar) [IsClosedImmersion i]
    (hcomp : Set.range D.j = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedInverseImage Λ i).map
      ((moduleUnboundedDerivedAdjunction Λ a.hom).unit.app
        ((moduleUnboundedDerivedLowerShriek D.j Λ).obj K))) := by
  let E := (moduleUnboundedDerivedLowerShriek D.j Λ).obj K
  let P := pullback a.hom i
  let p : P ⟶ Z := pullback.snd a.hom i
  let q : P ⟶ C.Xbar := pullback.fst a.hom i
  let := HasDerivedCategory.standard (ModuleSheaf P Λ)
  let sq : IsPullback q p a.hom i := IsPullback.of_hasPullback a.hom i
  have hbc : IsIso ((moduleUnboundedDerivedBaseChangeMap Λ a.hom p i q sq.w.symm).app
      ((moduleUnboundedDerivedInverseImage Λ a.hom).obj E)) := by
    let := Proper.properModuleUnboundedDerivedBaseChange_isIso
      Λ a.hom p i q sq N hN hΛ
    infer_instance
  have hz : IsZero ((moduleUnboundedDerivedInverseImage Λ i).obj E) :=
    isZero_moduleUnboundedDerivedInverseImage_lowerShriek D.j Λ i hcomp K
  have hunit : IsIso ((moduleUnboundedDerivedAdjunction Λ p).unit.app
      ((moduleUnboundedDerivedInverseImage Λ i).obj E)) :=
    hz.isIso ((moduleUnboundedDerivedDirectImage Λ p).map_isZero
      ((moduleUnboundedDerivedInverseImage Λ p).map_isZero hz)) _
  exact isIso_map_unit_of_iso_mate (moduleUnboundedDerivedAdjunction Λ a.hom)
    (moduleUnboundedDerivedAdjunction Λ p)
    (moduleUnboundedDerivedInverseImageSquareIso Λ a.hom p i q sq.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ a.hom p i q sq.w.symm) rfl E hbc hunit

/-- The original refinement comparison is invertible over the stated torsion ring,
using any actual complementary closed immersion for the target open. -/
theorem moduleUnboundedDerivedRefinementComparison_isIso_of_closedComplement
    {Z : Scheme.{u}} (i : Z ⟶ D.Xbar) [IsClosedImmersion i]
    (hcomp : Set.range D.j = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedRefinementComparison a Λ).app K) := by
  have hopen := refinementUnit_open_isIso a Λ N hN hΛ K
  have hclosed := refinementUnit_closed_isIso a Λ N hN hΛ i hcomp K
  let : IsIso ((moduleUnboundedDerivedAdjunction Λ a.hom).unit.app
      ((moduleUnboundedDerivedLowerShriek D.j Λ).obj K)) :=
    moduleUnboundedDerived_isIso_of_open_closed D.j Λ i hcomp
      ((moduleUnboundedDerivedAdjunction Λ a.hom).unit.app
        ((moduleUnboundedDerivedLowerShriek D.j Λ).obj K))
  rw [moduleUnboundedDerivedRefinementComparison_app]
  infer_instance

/-- Proper refinement preserves the original open extension by the original
unit comparison, for every unbounded object over the stated torsion ring. -/
theorem moduleUnboundedDerivedRefinementComparison_isIso
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedRefinementComparison a Λ).app K) := by
  let I := IdealSheafData.vanishingIdeal D.j.opensRange.compl
  let := HasDerivedCategory.standard (ModuleSheaf I.subscheme Λ)
  apply moduleUnboundedDerivedRefinementComparison_isIso_of_closedComplement
    a Λ N hN hΛ I.subschemeι
    (K := K)
  have hI : Set.range I.subschemeι = (Set.range D.j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  exact ((congrArg (fun T : Set D.Xbar => Tᶜ) hI).trans
    (compl_compl (Set.range D.j))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
