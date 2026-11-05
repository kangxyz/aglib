/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.AnnihilatorSingle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FullSubcategory
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # Original inverse images and annihilated singles

Additivity retains the specified coefficient annihilator. The exact-single
comparison lifts to the original native torsion range, keeping its original
maps and independent source and target derived realizations.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wY
attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- The original inverse image retains the actual positive-annihilator class. -/
def moduleAnnihilatedInverseImage (n : ℕ) :
    (moduleAnnihilated X Λ n).FullSubcategory ⥤
      (moduleAnnihilated Y Λ n).FullSubcategory :=
  ObjectProperty.lift (moduleAnnihilated Y Λ n)
    ((moduleAnnihilated X Λ n).ι ⋙ moduleInverseImage f Λ) (fun M => by
      let F := moduleInverseImage f Λ
      exact (F.map_nsmul.trans (congrArg (fun a => n • a) (F.map_id M.obj))).symm.trans
        ((congrArg F.map M.property).trans (F.map_zero M.obj M.obj)))

variable [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]

/-- The original exact-single comparison on the actual annihilator and native
torsion full subcategories. It changes neither coefficient nor arrow. -/
def moduleAnnihilatedInverseImageSingleIso (n : ℕ) (hn : 0 < n) :
    moduleAnnihilatedSingleFunctor X Λ n hn ⋙ moduleDerivedInverseImageTorsion f Λ ≅
      moduleAnnihilatedInverseImage f Λ n ⋙ moduleAnnihilatedSingleFunctor Y Λ n hn :=
  (moduleTorsionCohomologyPlus Y Λ).liftFunctorIso
    ((moduleAnnihilated X Λ n).ι ⋙
      DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0 ⋙ moduleDerivedInverseImage Λ f)
    ((moduleAnnihilated X Λ n).ι ⋙ moduleInverseImage f Λ ⋙
      DerivedCategory.Plus.singleFunctor (ModuleSheaf Y Λ) 0)
    (fun M => ((moduleDerivedInverseImageTorsion f Λ).obj
      ((moduleAnnihilatedSingleFunctor X Λ n hn).obj M)).property)
    (fun M => ((moduleAnnihilatedSingleFunctor Y Λ n hn).obj
      ((moduleAnnihilatedInverseImage f Λ n).obj M)).property)
    (Functor.isoWhiskerLeft (moduleAnnihilated X Λ n).ι
      ((moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIso 0))

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
