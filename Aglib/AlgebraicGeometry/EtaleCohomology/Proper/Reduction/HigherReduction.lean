/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.BoundedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SingleHigher

/-! # Reduction with the original all-degree sheaf exchange hypotheses

These direct consumers state composition and surjective descent entirely in
terms of the published natural-degree higher-image maps. The derived-single
criterion is discharged by the proved original homology transport and its
native nonnegative bounds. The coefficient quantifiers remain explicit on
the original source schemes.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dS dX dY dS' dX' dY'

attribute [local instance] hasSheafifyLarge

variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dY'} (AbelianSheaf.{u, u + 1} Y')]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (n : ℕ)

/-- Adjacent original all-degree exchange on all n-killed coefficients implies
the original composite higher exchange in every degree on every such coefficient. -/
theorem higherBaseChangeMap_comp_on_killedCoefficients
    (hOuter : ∀ (F : AbelianSheaf.{u, u + 1} X), n • 𝟙 F = 0 →
      ∀ q : ℕ, IsIso ((higherBaseChangeMap f f' g g' h₁ q).app F))
    (hInner : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      ∀ q : ℕ, IsIso ((higherBaseChangeMap k k' g' g'' h₂ q).app F))
    (F : AbelianSheaf.{u, u + 1} Y) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h q).app F) :=
  higherExchange_comp_on_killedCoefficients f k f' k' g g' g'' h₁ h₂ h n
    (fun G hG => (derivedBaseChangeMap_single_isIso_iff_higher f f' g g' h₁ G).mpr
      (hOuter G hG))
    (fun G hG => (derivedBaseChangeMap_single_isIso_iff_higher k k' g' g'' h₂ G).mpr
      (hInner G hG)) F hF q

/-- Along the actual surjection, original all-degree exchange for the source
and composite implies original all-degree exchange for the descended morphism
on every original coefficient annihilated by the specified modulus. -/
theorem higherBaseChangeMap_descent_on_killedCoefficients [Surjective k]
    (hInner : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      ∀ q : ℕ, IsIso ((higherBaseChangeMap k k' g' g'' h₂ q).app F))
    (hComposite : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      ∀ q : ℕ, IsIso ((higherBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h q).app F))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h₁ q).app F) :=
  higherExchange_descent_on_killedCoefficients f k f' k' g g' g'' h₁ h₂ h n
    (fun G hG => (derivedBaseChangeMap_single_isIso_iff_higher k k' g' g'' h₂ G).mpr
      (hInner G hG))
    (fun G hG =>
      (derivedBaseChangeMap_single_isIso_iff_higher (k ≫ f) (k' ≫ f') g g'' h G).mpr
        (hComposite G hG)) F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
