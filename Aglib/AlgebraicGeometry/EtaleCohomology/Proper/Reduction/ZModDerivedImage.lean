/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModAcyclic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.AcyclicSingle

/-! # The original derived image of a genuine injective module coefficient

Use the native coefficient-specific acyclic-single comparison, constructed
from the original installed derived unit, and the literal underlying module
direct-image comparison. The internal Ext existence is discharged at its
standard size; the two declared derived-category universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dX dS

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

/-- The actual bounded-below derived direct image of the underlying genuine
module injective is the single of its actual genuine module direct image.
The comparison is the native acyclic-single comparison from the original derived unit. -/
def derivedDirectImageZModInjectiveSingleIso
    {X S : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    (f : X ⟶ S) (n : ℕ) (I : ZModSheaf X n) [Injective I] :
    (derivedDirectImage f).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj
          ((zmodUnderlying X n).obj I)) ≅
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj
        ((zmodUnderlying S n).obj ((zmodDirectImage f n).obj I)) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X
  exact (directImage f).rightDerivedFunctorPlusSingleIsoOfAcyclic
    ((zmodUnderlying X n).obj I)
    (fun q => higherDirectImage_zmodInjective_isZero.{u, u + 2} f n I q) ≪≫
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).mapIso
        ((zmodDirectImageUnderlyingIso f n).app I).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
