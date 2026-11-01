/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SerreLeray
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Noetherian.StrongSerre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Composition

/-! # Constructibility under original composition from a finite diagonal

For a fixed total degree, constructibility of the actual iterated higher
images on its finite nonnegative diagonal implies constructibility of the
original composite higher image. The original derived composition and finite
Postnikov window are used. No finite inner map, global cohomological dimension,
or proper/smooth base-change premise is imposed; geometric diagonal suppliers
remain separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u dY dX dS

attribute [local instance] hasSheafifyLarge

variable {Y X S : Scheme.{u}} [IsNoetherian S]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

/-- The finite total-degree diagonal supplies constructibility of the same
original composite higher image, through its actual derived composition map.
The target alone is required to be Noetherian for the strong Serre property. -/
theorem higherDirectImage_isConstructible_of_composition_diagonal
    (f : X ⟶ S) (g : Y ⟶ X) (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ)
    (hdiag : ∀ j : ℕ, j ≤ q → Constructible.IsConstructible
      ((higherDirectImage f (q - j)).obj ((higherDirectImage g j).obj M))) :
    Constructible.IsConstructible ((higherDirectImage (g ≫ f) q).obj M) := by
  let K := (derivedDirectImage g).obj
    ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj M)
  let : K.IsGE 0 := (directImage g).rightDerivedFunctorPlus_isGE _ 0
  have hK : Constructible.IsConstructible
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).obj
        ((derivedDirectImage f).obj K)) := by
    apply (directImage f).rightDerived_property_of_homology_diagonal
      (Constructible.IsConstructible (X := S)) K q
    intro j hj
    exact (Constructible.isConstructible_iff_of_iso
      ((higherDirectImage f (q - j)).mapIso ((higherDirectImageIso g j).app M))).mp
        (hdiag j hj)
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)
  let e := (higherDirectImageIso (g ≫ f) q).app M ≪≫
    H.mapIso ((derivedDirectImageCompIso f g).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj M))
  exact (Constructible.isConstructible_iff_of_iso e).mpr hK

end AlgebraicGeometry.Scheme.EtaleCohomology
