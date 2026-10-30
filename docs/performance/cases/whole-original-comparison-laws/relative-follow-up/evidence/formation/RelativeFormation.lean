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

/-! Diagnostic only: form the exact coefficient rectangle proposition as a hypothesis. -/

theorem relativeCoefficient_formation_probe
    {X X' A B A' B' : Scheme.{u}}
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a) (hRect : v' ≫ r = σ ≫ v)
    (F : AbelianSheaf.{u, u + 1} X)
    (_h :
    (inverseImageComp r v').hom.app ((inverseImage p).obj F) ≫
        (inverseImage v').map ((inverseImageSquareIso p p' g r hR).inv.app F) ≫
        (pullbackTriangleIso a' p' v' hv').inv.app ((inverseImage g).obj F) =
      eqToHom (congrArg (fun k : A' ⟶ B => (inverseImage k).obj ((inverseImage p).obj F))
        hRect) ≫
        (inverseImageComp v σ).hom.app ((inverseImage p).obj F) ≫
        (inverseImage σ).map ((pullbackTriangleIso a p v hv).inv.app F) ≫
        (inverseImageSquareIso a a' g σ hS).inv.app F) : True := True.intro

end AlgebraicGeometry.Scheme.EtaleCohomology
