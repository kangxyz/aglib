/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleDirectImageValued
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleValuedDirectImageSquare

/-! # The original native direct-image square under the coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Whole inverse composition retains the same original valued comparison. -/
theorem moduleDirectImageCompIso_inv_valued_whole {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    Functor.whiskerRight (moduleDirectImageCompIso Λ f g).inv
        (moduleSheafEquivalence X Λ).inverse ≫ (moduleDirectImageComparison (g ≫ f) Λ).hom =
      (moduleDirectImageCompRightIso Λ f g).hom ≫
        Functor.whiskerLeft (moduleSheafEquivalence T Λ).inverse
          (moduleValuedDirectImageCompIso Λ f g).inv :=
  ValuedComparison.inverse_comparison
    ((Functor.whiskeringRight (ModuleSheaf T Λ) (ModuleSheaf X Λ)
      (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse)
    (moduleDirectImageCompIso Λ f g)
    (Functor.isoWhiskerLeft (moduleSheafEquivalence T Λ).inverse
      (moduleValuedDirectImageCompIso Λ f g))
    (moduleDirectImageComparison (g ≫ f) Λ).hom (moduleDirectImageCompRightIso Λ f g).hom
    (moduleDirectImageCompIso_hom_valued_whole Λ f g)

/-- Inverse composition also retains the original valued comparison. -/
@[reassoc]
theorem moduleDirectImageCompIso_inv_valued {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf T Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleDirectImageCompIso Λ f g).inv.app M) ≫
      (moduleDirectImageComparison (g ≫ f) Λ).hom.app M =
    (moduleDirectImageCompRightIso Λ f g).hom.app M ≫
      (moduleValuedDirectImageCompIso Λ f g).inv.app
        ((moduleSheafEquivalence T Λ).inverse.obj M) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app (moduleDirectImageCompIso_inv_valued_whole Λ f g) M

/-- Equality transport retains the whole original coefficient comparison. -/
theorem moduleDirectImageComparison_eqToHom_whole {X S : Scheme.{u}}
    {f g : X ⟶ S} (h : f = g) :
    Functor.whiskerRight
        (eqToIso (congrArg (fun k => moduleDirectImage k Λ) h)).hom
        (moduleSheafEquivalence S Λ).inverse ≫ (moduleDirectImageComparison g Λ).hom =
      (moduleDirectImageComparison f Λ).hom ≫
        Functor.whiskerLeft (moduleSheafEquivalence X Λ).inverse
          (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h)).hom :=
  ValuedComparison.comparison_eqToIso
    (fun k : X ⟶ S => moduleDirectImage k Λ)
    (fun k : X ⟶ S => moduleValuedDirectImage k Λ)
    (moduleSheafEquivalence X Λ).inverse (moduleSheafEquivalence S Λ).inverse
    (fun k => moduleDirectImageComparison k Λ) h

/-- The coefficient comparison respects transport along equality of scheme maps. -/
theorem moduleDirectImageComparison_eqToHom {X S : Scheme.{u}}
    {f g : X ⟶ S} (h : f = g) (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence S Λ).inverse.map
        ((eqToIso (congrArg (fun k => moduleDirectImage k Λ) h)).hom.app M) ≫
      (moduleDirectImageComparison g Λ).hom.app M =
    (moduleDirectImageComparison f Λ).hom.app M ≫
      (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h)).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app (moduleDirectImageComparison_eqToHom_whole Λ h) M

/-- The native square retains its original functor-category composite. -/
theorem moduleDirectImageSquareIso_eq_comp {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    moduleDirectImageSquareIso Λ f f' g g' h =
      (moduleDirectImageCompIso Λ f g').symm ≪≫
        eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm) ≪≫
        moduleDirectImageCompIso Λ g f' := rfl

/-- The native square on components is the original three-factor composite. -/
theorem moduleDirectImageSquareIso_hom_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (M : ModuleSheaf X' Λ) :
    (moduleDirectImageSquareIso Λ f f' g g' h).hom.app M =
      (moduleDirectImageCompIso Λ f g').inv.app M ≫
        (eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm)).hom.app M ≫
        (moduleDirectImageCompIso Λ g f').hom.app M := by
  have he := congrArg (fun α :
      moduleDirectImage g' Λ ⋙ moduleDirectImage f Λ ≅
        moduleDirectImage f' Λ ⋙ moduleDirectImage g Λ => α.hom.app M)
    (moduleDirectImageSquareIso_eq_comp Λ f f' g g' h)
  exact he.trans (ValuedComparison.inverse_iso_chain_app (moduleDirectImageCompIso Λ f g')
    (eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm))
    (moduleDirectImageCompIso Λ g f') M)

/-- The valued square on components is the original three-factor composite. -/
theorem moduleValuedDirectImageSquareIso_hom_comp_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (F : ModuleValuedSheaf X' Λ) :
    (moduleValuedDirectImageSquareIso f f' g g' h Λ).hom.app F =
      (moduleValuedDirectImageCompIso Λ f g').inv.app F ≫
        (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h.symm)).hom.app F ≫
        (moduleValuedDirectImageCompIso Λ g f').hom.app F := by
  have he := congrArg (fun e :
      moduleValuedDirectImage g' Λ ⋙ moduleValuedDirectImage f Λ ≅
        moduleValuedDirectImage f' Λ ⋙ moduleValuedDirectImage g Λ => e.hom.app F)
    (moduleValuedDirectImageSquareIso_comp f f' g g' h Λ)
  exact he.symm

/-- The whole native square is the whole original valued site square after transport. -/
theorem moduleDirectImageSquareIso_hom_valued_whole {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    Functor.whiskerRight (moduleDirectImageSquareIso Λ f f' g g' h).hom
        (moduleSheafEquivalence S Λ).inverse ≫ (moduleDirectImageCompRightIso Λ g f').hom =
      (moduleDirectImageCompRightIso Λ f g').hom ≫
        Functor.whiskerLeft (moduleSheafEquivalence X' Λ).inverse
          (moduleValuedDirectImageSquareIso f f' g g' h Λ).hom := by
  refine ValuedComparison.comparison_square_of_aliases
    ((Functor.whiskeringRight (ModuleSheaf X' Λ) (ModuleSheaf S Λ)
      (ModuleValuedSheaf S Λ)).obj (moduleSheafEquivalence S Λ).inverse)
    (moduleDirectImageCompIso Λ f g') (moduleDirectImageCompIso Λ g f')
    (Functor.isoWhiskerLeft (moduleSheafEquivalence X' Λ).inverse
      (moduleValuedDirectImageCompIso Λ f g'))
    (Functor.isoWhiskerLeft (moduleSheafEquivalence X' Λ).inverse
      (moduleValuedDirectImageCompIso Λ g f'))
    (moduleDirectImageComparison (g' ≫ f) Λ).hom
    (moduleDirectImageComparison (f' ≫ g) Λ).hom
    (moduleDirectImageCompRightIso Λ f g').hom (moduleDirectImageCompRightIso Λ g f').hom
    (eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.symm)).hom
    (Functor.whiskerLeft (moduleSheafEquivalence X' Λ).inverse
      (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h.symm)).hom)
    (moduleDirectImageSquareIso Λ f f' g g' h)
    (Functor.isoWhiskerLeft (moduleSheafEquivalence X' Λ).inverse
      (moduleValuedDirectImageSquareIso f f' g g' h Λ)) ?_ ?_
    (moduleDirectImageCompIso_inv_valued_whole Λ f g')
    (moduleDirectImageCompIso_hom_valued_whole Λ g f')
    (moduleDirectImageComparison_eqToHom_whole Λ h.symm)
  · exact congrArg Iso.hom (moduleDirectImageSquareIso_eq_comp Λ f f' g g' h)
  · have hv := congrArg (fun e =>
        (Functor.isoWhiskerLeft (moduleSheafEquivalence X' Λ).inverse e).hom)
        (moduleValuedDirectImageSquareIso_comp f f' g g' h Λ).symm
    simpa only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp] using hv

/-- The original native direct-image square is the original valued site square after
transport through the actual constant-coefficient equivalence. -/
@[reassoc]
theorem moduleDirectImageSquareIso_hom_valued {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (M : ModuleSheaf X' Λ) :
    (moduleSheafEquivalence S Λ).inverse.map
        ((moduleDirectImageSquareIso Λ f f' g g' h).hom.app M) ≫
      (moduleDirectImageCompRightIso Λ g f').hom.app M =
    (moduleDirectImageCompRightIso Λ f g').hom.app M ≫
      (moduleValuedDirectImageSquareIso f f' g g' h Λ).hom.app
        ((moduleSheafEquivalence X' Λ).inverse.obj M) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app (moduleDirectImageSquareIso_hom_valued_whole Λ f f' g g' h) M

end AlgebraicGeometry.Scheme.EtaleCohomology
