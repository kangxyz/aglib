/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModulePullbackCoherence

/-! # Original native direct-image composition coherence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Native direct image retains the original underlying coefficient sheaf object. -/
theorem moduleDirectImage_underlying_obj {X S : Scheme.{u}} (f : S ⟶ X)
    (M : ModuleSheaf S Λ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).obj ((moduleDirectImage f Λ).obj M) =
      (directImage f).obj ((SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).obj M) := rfl

/-- Native direct image acts by the original direct image on underlying coefficient maps. -/
theorem moduleDirectImage_underlying_map {X S : Scheme.{u}} (f : S ⟶ X)
    {M N : ModuleSheaf S Λ} (a : M ⟶ N) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map ((moduleDirectImage f Λ).map a) =
      (directImage f).map ((SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).map a) := rfl

/-- The native composition comparison retains the original abelian direct-image comparison. -/
theorem moduleDirectImageCompIso_inv_underlying {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf T Λ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
      ((moduleDirectImageCompIso Λ f g).inv.app M) =
    (directImageCompIso f g).hom.app
      ((SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).obj M) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact moduleDirectImageCompIso_inv_app_apply Λ f g M U x

/-- Native direct-image composition associates with the original base-map equality transport. -/
@[reassoc]
theorem moduleDirectImageCompIso_assoc_app {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) (M : ModuleSheaf V Λ) :
    (moduleDirectImage f Λ).map ((moduleDirectImageCompIso Λ g h).inv.app M) ≫
        (moduleDirectImageCompIso Λ f (h ≫ g)).inv.app M ≫
        (eqToIso (congrArg (fun k => (moduleDirectImage k Λ).obj M)
          (Category.assoc h g f))).hom =
      (moduleDirectImageCompIso Λ f g).inv.app ((moduleDirectImage h Λ).obj M) ≫
        (moduleDirectImageCompIso Λ (g ≫ f) h).inv.app M := by
  apply (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map_injective
  simpa only [Functor.map_comp, moduleDirectImage_underlying_map,
    moduleDirectImageCompIso_inv_underlying, eqToIso.hom, eqToHom_map,
    Functor.comp_obj, moduleDirectImage_underlying_obj] using
    directImageCompIso_assoc_app f g h
      ((SheafOfModules.toSheaf.{u + 1} (constantRing V Λ)).obj M)

end AlgebraicGeometry.Scheme.EtaleCohomology
