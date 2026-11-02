/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionAssociativity

/-! # Original torsion compositors with explicit composite-arrow equalities -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wY wZ wV
variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original compositor after the specified equality of its composite arrow. -/
def moduleDerivedInverseImageTorsionCompEqIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (hk : k = g ≫ f)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)] :
    moduleDerivedInverseImageTorsion k Λ ≅
      moduleDerivedInverseImageTorsion f Λ ⋙ moduleDerivedInverseImageTorsion g Λ :=
  eqToIso (congrArg (fun z => moduleDerivedInverseImageTorsion z Λ) hk) ≪≫
    moduleDerivedInverseImageTorsionCompIso Λ f g

/-- Equality-normalized original compositors associate with every displayed
composite arrow retained. No coherence is imposed beyond the native theorem. -/
theorem moduleDerivedInverseImageTorsionCompEqIso_assoc {X Y Z V : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : V ⟶ Z)
    (fg : Z ⟶ X) (gh : V ⟶ Y) (fgh : V ⟶ X)
    (hfg : fg = g ≫ f) (hgh : gh = h ≫ g)
    (hl : fgh = gh ≫ f) (hr : fgh = h ≫ fg)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    moduleDerivedInverseImageTorsionCompEqIso Λ f gh fgh hl ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion f Λ)
          (moduleDerivedInverseImageTorsionCompEqIso Λ g h gh hgh) =
      moduleDerivedInverseImageTorsionCompEqIso Λ fg h fgh hr ≪≫
        Functor.isoWhiskerRight (moduleDerivedInverseImageTorsionCompEqIso Λ f g fg hfg)
          (moduleDerivedInverseImageTorsion h Λ) ≪≫
        Functor.associator (moduleDerivedInverseImageTorsion f Λ)
          (moduleDerivedInverseImageTorsion g Λ) (moduleDerivedInverseImageTorsion h Λ) := by
  subst fg
  subst gh
  subst hl
  simpa only [moduleDerivedInverseImageTorsionCompEqIso, eqToIso_refl, Iso.refl_trans,
    Iso.trans_assoc, Functor.CompositionAssociates] using
      moduleDerivedInverseImageTorsionCompIso_assoc Λ f g h

end AlgebraicGeometry.Scheme.EtaleCohomology
