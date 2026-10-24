/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleBaseChangeUnit

/-! # Composition description of the actual module-valued direct-image square -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

local instance {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    (siteBaseChange f ⋙ siteBaseChange g).IsContinuous
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology T) :=
  Functor.isContinuous_comp (siteBaseChange f) (siteBaseChange g)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (Scheme.smallEtaleTopology T)

private theorem valuedComp_inv_transform {X S T : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] (f : S ⟶ X) (g : T ⟶ S) :
    (moduleValuedDirectImageCompIso Λ f g).inv =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).hom
        (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.id_comp _

private theorem valuedComp_hom_transform {X S T : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] (f : S ⟶ X) (g : T ⟶ S) :
    (moduleValuedDirectImageCompIso Λ f g).hom =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).inv
        (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.comp_id _

private theorem valuedEqToIso_transform {X S : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] {f g : S ⟶ X} (h : f = g) :
    (eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h)).hom =
      Functor.sheafPushforwardContinuousNatTrans
        (eqToHom (congrArg (fun k => siteBaseChange k) h.symm))
        (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology S) := by
  subst g
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (𝟙 _) = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

/-- The original composition comparisons give the coefficient-free site square. -/
theorem moduleValuedDirectImageSquareIso_comp {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (Λ : Type (u + 1)) [Ring Λ] :
    (moduleValuedDirectImageCompIso Λ f g').symm ≪≫
      eqToIso (congrArg (fun k => moduleValuedDirectImage k Λ) h.symm) ≪≫
        moduleValuedDirectImageCompIso Λ g f' =
      moduleValuedDirectImageSquareIso f f' g g' h Λ := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, valuedComp_inv_transform,
    valuedComp_hom_transform]
  rw [valuedEqToIso_transform Λ h.symm]
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChangeComp f g').hom.app U.unop).op ≫
      F.obj.map ((eqToHom (congrArg (fun k => siteBaseChange k) h)).app U.unop).op ≫
        F.obj.map ((siteBaseChangeComp g f').inv.app U.unop).op =
      F.obj.map ((siteBaseChangeSquareIso f f' g g' h).hom.app U.unop).op
  simp only [siteBaseChangeSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, op_comp, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
