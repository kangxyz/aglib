/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Composition

/-! # Original higher-image composition with a finite inner morphism

The original derived composition comparison and the exact finite direct-image
single comparison identify the same natural-degree images. No proper or smooth
base-change theorem is used, and the coefficient is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u dY dX dS

attribute [local instance] hasSheafifyLarge

variable {Y X S : Scheme.{u}}
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

/-- Composition with the original exact finite direct image, on the same
coefficient and with all three derived-category universes retained. -/
def higherDirectImageCompFiniteIso (f : X ⟶ S) (k : Y ⟶ X) [IsFinite k]
    (q : ℕ) (M : AbelianSheaf.{u, u + 1} Y) :
    (higherDirectImage (k ≫ f) q).obj M ≅
      (higherDirectImage f q).obj ((directImage k).obj M) := by
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)
  let K := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj M
  exact (higherDirectImageIso (k ≫ f) q).app M ≪≫
    H.mapIso ((derivedDirectImageCompIso f k).app K) ≪≫
    H.mapIso ((derivedDirectImage f).mapIso ((derivedDirectImageSingleIso k 0).app M)) ≪≫
    ((higherDirectImageIso f q).app ((directImage k).obj M)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
