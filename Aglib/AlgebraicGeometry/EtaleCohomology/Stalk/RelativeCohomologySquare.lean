/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseRectangle
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection
public import Aglib.CategoryTheory.Abelian.Ext.CoefficientSquare

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

/-- The whole triangle-square law is on the five original native comparisons,
before selecting a coefficient object. -/
private theorem relativeCohomologySquare_whole
    {X X' A B A' B' : Scheme.{u}}
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a) (hRect : v' ≫ r = σ ≫ v) :
    Adjunction.CoefficientSquares.WholeTriangleSquareEquation
      (pullbackTriangleIso a p v hv) (pullbackTriangleIso a' p' v' hv')
      (inverseImageSquareIso p p' g r hR).symm
      (inverseImageSquareIso a a' g σ hS) (inverseImageSquareIso v v' r σ hRect) := by
  refine schemeAdjunctionData.triangleSquare_whole_of_eq schemeAdjunctionData_coherent
    p.op p'.op g.op r.op σ.op a.op v.op a'.op v'.op
    (congrArg Quiver.Hom.op hR.symm) (congrArg Quiver.Hom.op hv)
    (congrArg Quiver.Hom.op hv') (congrArg Quiver.Hom.op hS) (congrArg Quiver.Hom.op hRect)
    (pullbackTriangleIso a p v hv) (pullbackTriangleIso a' p' v' hv')
    (inverseImageSquareIso p p' g r hR).symm
    (inverseImageSquareIso a a' g σ hS) (inverseImageSquareIso v v' r σ hRect)
    ?_ ?_ ?_ ?_ ?_
  · simpa only [Quiver.Hom.unop_op] using
      (schemeTriangleIso_eq_pullbackTriangleIso p.op a.op v.op
        (congrArg Quiver.Hom.op hv)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeTriangleIso_eq_pullbackTriangleIso p'.op a'.op v'.op
        (congrArg Quiver.Hom.op hv')).symm
  · have hs := schemeSquareIso_eq_inverseImageSquareIso g.op r.op p.op p'.op
      (congrArg Quiver.Hom.op hR.symm)
    simp only [Quiver.Hom.unop_op] at hs
    exact (hs.trans (inverseImageSquareIso_transpose p p' g r hR)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeSquareIso_eq_inverseImageSquareIso a.op a'.op g.op σ.op
        (congrArg Quiver.Hom.op hS)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeSquareIso_eq_inverseImageSquareIso v.op v'.op r.op σ.op
        (congrArg Quiver.Hom.op hRect)).symm

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
  exact InjectiveSystem.AdjunctionData.inverse_triangle_coefficient_of_whole
    (pullbackTriangleIso a p v hv) (pullbackTriangleIso a' p' v' hv')
    (inverseImageSquareIso p p' g r hR).symm
    (inverseImageSquareIso a a' g σ hS) (inverseImageSquareIso v v' r σ hRect)
    (relativeCohomologySquare_whole p p' a a' v v' r σ g hv hv' hR hS hRect)
    (fun k : A' ⟶ B => inverseImage k) hRect
    (inverseImageComp r v') (inverseImageComp v σ)
    (inverseImageSquareIso_eq_comp v v' r σ hRect) F

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
      cohomologyTransfer v χ q ≫ cohomologyTransfer σ δS q :=
  by
  have hleft := cohomologyTransfer_comp r v' δR χ' q
  have hright := cohomologyTransfer_comp v σ χ δS q
  have hcoefficient := congrArg
    (fun φ : (inverseImage (v' ≫ r)).obj F ⟶ K => cohomologyTransfer (v' ≫ r) φ q)
    hCoeff
  have htransport := cohomologyTransfer_transport (σ ≫ v) (v' ≫ r) hRect
    ((inverseImageComp v σ).hom.app F ≫ (inverseImage σ).map χ ≫ δS) q
  exact hleft.trans (hcoefficient.trans (htransport.trans hright.symm))

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
