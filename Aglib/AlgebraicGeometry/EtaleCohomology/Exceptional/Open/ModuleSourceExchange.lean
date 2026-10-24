/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate

/-! # Original exchange for a change of source -/

@[expose] public noncomputable section

open CategoryTheory

private theorem normalized_identity_square_app
    {C D : Type*} [Category* C] [Category* D]
    {F H : C ⥤ D} {I : C ⥤ C}
    (a : F ≅ I ⋙ H) (e : I ≅ 𝟭 C) (b : F ≅ H)
    (h : a ≪≫ Functor.isoWhiskerRight e H ≪≫ Functor.leftUnitor H = b) (M : C) :
    a.hom.app M ≫ H.map (e.hom.app M) = b.hom.app M := by
  have hc := congrArg (fun z : F ≅ H => z.hom.app M) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hc
  exact (congrArg (fun z => a.hom.app M ≫ z)
    (Category.comp_id (H.map (e.hom.app M)))).symm.trans hc

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

/-- The original counit equation for an arbitrary native inverse-image square. -/
theorem moduleExchange_counit {X X' S S' : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (α : moduleInverseImage g Λ ⋙ moduleInverseImage f' Λ ⟶
      moduleInverseImage f Λ ⋙ moduleInverseImage g' Λ) (M : ModuleSheaf X Λ) :
    (moduleInverseImage f' Λ).map
        (((mateEquiv (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
          (TwoSquare.mk _ _ _ _ α)).natTrans).app M) ≫
      (moduleInverseImageAdjunction f' Λ).counit.app
        ((moduleInverseImage g' Λ).obj M) =
    α.app ((moduleDirectImage f Λ).obj M) ≫
      (moduleInverseImage g' Λ).map ((moduleInverseImageAdjunction f Λ).counit.app M) :=
  mateEquiv_counit (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (TwoSquare.mk _ _ _ _ α) M

variable {V P Y : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  (p : P ⟶ Y) (e : V ⟶ P) (i : V ⟶ Y) (he : e ≫ p = i)

/-- The original inverse-image comparison for a factorization of the source map. -/
def moduleSourceInverseImageIso :
    moduleInverseImage i Λ ≅ moduleInverseImage p Λ ⋙ moduleInverseImage e Λ :=
  eqToIso (congrArg (fun k => moduleInverseImage k Λ) he.symm) ≪≫
    moduleInverseImageCompIso Λ p e

/-- The whole identity-side square retains the original source comparison. -/
theorem moduleInverseImageSquareIso_source_iso :
    moduleInverseImageSquareIso Λ (𝟙 Y) e p i
        (he.trans (Category.comp_id i).symm) ≪≫
      Functor.isoWhiskerRight (moduleInverseImageIdIso Λ Y) (moduleInverseImage i Λ) ≪≫
      Functor.leftUnitor (moduleInverseImage i Λ) =
    (moduleSourceInverseImageIso Λ p e i he).symm := by
  apply Iso.ext
  have h := congrArg Iso.hom (moduleInverseImageCompIso_id_comp Λ i)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom] at h
  simp only [moduleInverseImageSquareIso, moduleSourceInverseImageIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Category.assoc]
  rw [h]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_trans]

/-- The identity-side inverse-image square is the original source comparison. -/
@[reassoc]
theorem moduleInverseImageSquareIso_source (M : ModuleSheaf Y Λ) :
    (moduleInverseImageSquareIso Λ (𝟙 Y) e p i
        (he.trans (Category.comp_id i).symm)).hom.app M ≫
      (moduleInverseImage i Λ).map ((moduleInverseImageIdIso Λ Y).hom.app M) =
    (moduleSourceInverseImageIso Λ p e i he).inv.app M :=
  normalized_identity_square_app _ _ _
    (moduleInverseImageSquareIso_source_iso Λ p e i he) M

/-- A change of source retains the exact original unit of that source map. -/
@[reassoc]
theorem moduleBaseChangeMap_source (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ (𝟙 Y) e p i
      (he.trans (Category.comp_id i).symm)).app M =
    (moduleInverseImage p Λ).map ((moduleDirectImageIdIso Λ Y).hom.app M) ≫
      (moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage p Λ).obj M) ≫
      (moduleDirectImage e Λ).map ((moduleSourceInverseImageIso Λ p e i he).inv.app M) := by
  let a := moduleInverseImageAdjunction e Λ
  let t : (moduleInverseImage p Λ).obj ((moduleDirectImage (𝟙 Y) Λ).obj M) ⟶
      (moduleInverseImage p Λ).obj M :=
    (moduleInverseImage p Λ).map ((moduleDirectImageIdIso Λ Y).hom.app M)
  let k := (moduleInverseImage e Λ).map t ≫
    (moduleSourceInverseImageIso Λ p e i he).inv.app M
  have hb : (moduleBaseChangeMap Λ (𝟙 Y) e p i
      (he.trans (Category.comp_id i).symm)).app M = a.homEquiv _ _ k := by
    apply (a.homEquiv _ _).symm.injective
    simp only [Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
    change (moduleInverseImage e Λ).map _ ≫
      (moduleInverseImageAdjunction e Λ).counit.app _ = k
    dsimp only [moduleBaseChangeMap]
    rw [moduleExchange_counit Λ (𝟙 Y) e p i]
    rw [moduleInverseImageIdIso_counit Λ Y M, Functor.map_comp]
    rw [reassoc_of% (moduleInverseImageSquareIso_source Λ p e i he
      ((moduleDirectImage (𝟙 Y) Λ).obj M))]
    have hn := (moduleSourceInverseImageIso Λ p e i he).inv.naturality
      ((moduleDirectImageIdIso Λ Y).hom.app M)
    simp only [Functor.comp_map] at hn
    exact hn.symm
  rw [hb]
  change a.unit.app _ ≫ (moduleDirectImage e Λ).map k = _
  dsimp only [k]
  rw [Functor.map_comp, ← Category.assoc]
  have hu := a.unit_naturality t
  exact (congrArg (fun z => z ≫ (moduleDirectImage e Λ).map
    ((moduleSourceInverseImageIso Λ p e i he).inv.app M)) hu).trans
      (Category.assoc _ _ _)

end AlgebraicGeometry.Scheme.EtaleCohomology
