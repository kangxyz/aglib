/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.AnnihilatorCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Original annihilated singles in the native torsion range

The ring itself need not be torsion or finite. The literal positive annihilator
of the original coefficient is mapped through the original single and homology
functors, then detected on actual sections of the original underlying sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- A positive annihilator of an actual derived identity gives torsion of every
original homology object, without any scalar-unit annihilator assumption. -/
theorem moduleTorsionCohomology_of_nsmul_id_eq_zero
    (K : DerivedCategory (ModuleSheaf X Λ)) (n : ℕ) (hn : 0 < n)
    (hK : n • 𝟙 K = 0) : moduleTorsionCohomology X Λ K := by
  intro q
  let H := DerivedCategory.homologyFunctor (ModuleSheaf X Λ) q ⋙
    SheafOfModules.toSheaf (constantRing X Λ)
  apply Sheaf.isTorsion_of_nsmul_id_eq_zero (H.obj K) n hn
  exact (H.map_nsmul.trans (congrArg (fun a => n • a) (H.map_id K))).symm.trans
    ((congrArg H.map hK).trans (H.map_zero K K))

/-- Original positive-annihilated coefficients, retaining all original arrows. -/
def moduleAnnihilated (n : ℕ) : ObjectProperty (ModuleSheaf X Λ) :=
  fun M => n • 𝟙 M = 0

/-- The original degree-zero single of an annihilated coefficient is internally
torsion in the actual supplied derived realization. -/
theorem moduleTorsionSingle_of_annihilator
    (M : ModuleSheaf X Λ) (n : ℕ) (hn : 0 < n) (hM : n • 𝟙 M = 0) :
    moduleTorsionCohomologyPlus X Λ
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj M) := by
  let L := DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0 ⋙
    DerivedCategory.Plus.ι
  apply moduleTorsionCohomology_of_nsmul_id_eq_zero X Λ (L.obj M) n hn
  exact (L.map_nsmul.trans (congrArg (fun a => n • a) (L.map_id M))).symm.trans
    ((congrArg L.map hM).trans (L.map_zero M M))

/-- The original single functor on the original annihilator full subcategory,
with only its codomain lifted into the actual torsion-cohomology range. -/
def moduleAnnihilatedSingleFunctor (n : ℕ) (hn : 0 < n) :
    (moduleAnnihilated X Λ n).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  ObjectProperty.lift (moduleTorsionCohomologyPlus X Λ)
    ((moduleAnnihilated X Λ n).ι ⋙ DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0)
    (fun M => moduleTorsionSingle_of_annihilator X Λ M.obj n hn M.property)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
