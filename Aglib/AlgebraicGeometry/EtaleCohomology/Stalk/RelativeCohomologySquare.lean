/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Original cohomology transfers on a relative rectangle

The original inverse-image square and triangle comparisons satisfy the
coefficient rectangle, including transport along its actual arrow equality.
The original cohomology transfers therefore commute in every natural degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e

attribute [local instance] hasSheafifyLarge

open Continuity

private theorem five_iso_inverse {C : Type*} [Category* C] {A B D E F : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : A ≅ F) (e : F ≅ E)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) :
    b.inv ≫ a.inv = c.hom ≫ e.inv ≫ d.inv := by
  have he : a ≪≫ b ≪≫ c = d ≪≫ e := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Category.assoc] using h
  have hi : c.inv ≫ b.inv ≫ a.inv = e.inv ≫ d.inv := by
    simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv he
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
    congrArg (fun k => c.hom ≫ k) hi

private theorem five_iso_inverse_prefixed {C : Type*} [Category* C]
    {A B D E F K L : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : A ≅ F) (e : F ≅ E)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom)
    (s : K ⟶ D) (t : K ⟶ L) (j : L ⟶ E) (hs : s ≫ c.hom = t ≫ j) :
    s ≫ b.inv ≫ a.inv = t ≫ j ≫ e.inv ≫ d.inv := by
  rw [five_iso_inverse a b c d e h]
  calc
    _ = (s ≫ c.hom) ≫ e.inv ≫ d.inv := by simp only [Category.assoc]
    _ = (t ≫ j) ≫ e.inv ≫ d.inv := congrArg (fun k => k ≫ e.inv ≫ d.inv) hs
    _ = _ := by simp only [Category.assoc]

private theorem square_factorization_app {C D A : Type*} [Category* C] [Category* D]
    (P : A → C ⥤ D) (s t : A) (h : s = t) {U V : C ⥤ D}
    (a : P s ≅ U) (b : P t ≅ V) (d : U ≅ V)
    (hd : d = a.symm ≪≫ eqToIso (congrArg P h) ≪≫ b) (M : C) :
    a.hom.app M ≫ d.hom.app M =
      eqToHom (congrArg (fun k => (P k).obj M) h) ≫ b.hom.app M := by
  subst d
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Iso.hom_inv_id_app_assoc]

private theorem relative_square_composite_coefficient
    {X X' A B A' B' : Scheme.{u}}
    (p : B ⟶ X) (p' : B' ⟶ X') (v : A ⟶ B) (v' : A' ⟶ B')
    (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hR : p' ≫ g = r ≫ p) (hS : (v' ≫ p') ≫ g = σ ≫ (v ≫ p))
    (hRect : v' ≫ r = σ ≫ v) (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp r v').hom.app ((inverseImage p).obj F) ≫
        (inverseImage v').map ((inverseImageSquareIso p p' g r hR).inv.app F) ≫
        (inverseImageComp p' v').inv.app ((inverseImage g).obj F) =
      eqToHom (congrArg (fun k : A' ⟶ B => (inverseImage k).obj ((inverseImage p).obj F))
        hRect) ≫
        (inverseImageComp v σ).hom.app ((inverseImage p).obj F) ≫
        (inverseImage σ).map ((inverseImageComp p v).inv.app F) ≫
        (inverseImageSquareIso (v ≫ p) (v' ≫ p') g σ hS).inv.app F := by
  exact five_iso_inverse_prefixed
    ((inverseImageComp p' v').app ((inverseImage g).obj F))
    ((inverseImage v').mapIso ((inverseImageSquareIso p p' g r hR).app F))
    ((inverseImageSquareIso v v' r σ hRect).app ((inverseImage p).obj F))
    ((inverseImageSquareIso (v ≫ p) (v' ≫ p') g σ hS).app F)
    ((inverseImage σ).mapIso ((inverseImageComp p v).app F))
    (inverseImageSquareIso_vComp p v p' v' g r σ hR hRect hS F)
    ((inverseImageComp r v').hom.app ((inverseImage p).obj F))
    (eqToHom (congrArg (fun k : A' ⟶ B => (inverseImage k).obj ((inverseImage p).obj F))
      hRect))
    ((inverseImageComp v σ).hom.app ((inverseImage p).obj F))
    (square_factorization_app (fun k : A' ⟶ B => inverseImage k)
      (v' ≫ r) (σ ≫ v) hRect
      (inverseImageComp r v') (inverseImageComp v σ)
      (inverseImageSquareIso v v' r σ hRect)
      (inverseImageSquareIso_eq_comp v v' r σ hRect) ((inverseImage p).obj F))

/-- The literal square and triangle coefficient maps commute after the actual
rectangle arrow transport. No geometric base-change hypothesis is required. -/
theorem relativeCohomologySquare_coefficient
    {X X' A B A' B' : Scheme.{u}}
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a) (hRect : v' ≫ r = σ ≫ v)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp r v').hom.app ((inverseImage p).obj F) ≫
        (inverseImage v').map ((inverseImageSquareIso p p' g r hR).inv.app F) ≫
        (pullbackTriangleIso a' p' v' hv').inv.app ((inverseImage g).obj F) =
      eqToHom (congrArg (fun k : A' ⟶ B => (inverseImage k).obj ((inverseImage p).obj F))
        hRect) ≫
        (inverseImageComp v σ).hom.app ((inverseImage p).obj F) ≫
        (inverseImage σ).map ((pullbackTriangleIso a p v hv).inv.app F) ≫
        (inverseImageSquareIso a a' g σ hS).inv.app F := by
  subst a
  subst a'
  simpa only [pullbackTriangleIso, eqToIso_refl, Iso.refl_trans] using
    relative_square_composite_coefficient p p' v v' r σ g hR hS hRect F

private theorem transfer_square_of_coefficients {A B A' B' : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B')]
    (r : B' ⟶ B) (v' : A' ⟶ B') (v : A ⟶ B) (σ : A' ⟶ A)
    (hRect : v' ≫ r = σ ≫ v)
    {F : AbelianSheaf.{u, u + 1} B} {G : AbelianSheaf.{u, u + 1} B'}
    {H : AbelianSheaf.{u, u + 1} A} {K : AbelianSheaf.{u, u + 1} A'}
    (δR : (inverseImage r).obj F ⟶ G) (χ' : (inverseImage v').obj G ⟶ K)
    (χ : (inverseImage v).obj F ⟶ H) (δS : (inverseImage σ).obj H ⟶ K)
    (hCoeff : (inverseImageComp r v').hom.app F ≫ (inverseImage v').map δR ≫ χ' =
      eqToHom (congrArg (fun k : A' ⟶ B => (inverseImage k).obj F) hRect) ≫
        (inverseImageComp v σ).hom.app F ≫ (inverseImage σ).map χ ≫ δS) (q : ℕ) :
    cohomologyTransfer r δR q ≫ cohomologyTransfer v' χ' q =
      cohomologyTransfer v χ q ≫ cohomologyTransfer σ δS q := by
  exact (cohomologyTransfer_comp r v' δR χ' q).trans
    ((congrArg (fun k : (inverseImage (v' ≫ r)).obj F ⟶ K =>
      cohomologyTransfer (v' ≫ r) k q) hCoeff).trans
        ((cohomologyTransfer_transport (σ ≫ v) (v' ≫ r) hRect
          ((inverseImageComp v σ).hom.app F ≫ (inverseImage σ).map χ ≫ δS) q).trans
            (cohomologyTransfer_comp v σ χ δS q).symm))

/-- The original transfers across a relative rectangle commute in every natural
degree, with the original square inverses and triangle inverses as coefficients. -/
theorem cohomologyTransfer_relative_square
    {X X' A B A' B' : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B')]
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a) (hRect : v' ≫ r = σ ≫ v)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    cohomologyTransfer r ((inverseImageSquareIso p p' g r hR).inv.app F) q ≫
        cohomologyTransfer v'
          ((pullbackTriangleIso a' p' v' hv').inv.app ((inverseImage g).obj F)) q =
      cohomologyTransfer v ((pullbackTriangleIso a p v hv).inv.app F) q ≫
        cohomologyTransfer σ ((inverseImageSquareIso a a' g σ hS).inv.app F) q := by
  exact transfer_square_of_coefficients r v' v σ hRect
    ((inverseImageSquareIso p p' g r hR).inv.app F)
    ((pullbackTriangleIso a' p' v' hv').inv.app ((inverseImage g).obj F))
    ((pullbackTriangleIso a p v hv).inv.app F)
    ((inverseImageSquareIso a a' g σ hS).inv.app F)
    (relativeCohomologySquare_coefficient p p' a a' v v' r σ g hv hv' hR hS hRect F) q

end AlgebraicGeometry.Scheme.EtaleCohomology
