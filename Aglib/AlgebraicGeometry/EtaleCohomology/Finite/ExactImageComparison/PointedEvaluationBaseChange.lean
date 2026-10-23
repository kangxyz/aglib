/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointedStalkSquare

/-! # Canonical ordinary exchange on original pointed direct-image evaluations -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge
open CoefficientStalkBaseChange

variable {X S X' S' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Original direct-image evaluation at a compatible geometric point is the
original stalk unit followed by the original adjunction counit on that stalk. -/
def pointedDirectImageEvaluation (f : X ⟶ S) (x : Spec (.of Ω) ⟶ X)
    (s : Spec (.of Ω) ⟶ S) (hx : x ≫ f = s) (F : AbelianSheaf.{u, u + 1} X) :
    coefficientFiber s ((directImage f).obj F) ⟶ coefficientFiber x F :=
  pointedStalkUnit f x ((directImage f).obj F) s hx ≫
    (pointSmallEtale x).sheafFiber.map ((inverseImageAdjunction f).counit.app F)

/-- The literal ordinary mate commutes with actual pointed evaluation in every
coordinate. No invertibility of the exchange is assumed. -/
theorem pointedDirectImageEvaluation_baseChange
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f)
    (x : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ S)
    (x' : Spec (.of Ω) ⟶ X') (s' : Spec (.of Ω) ⟶ S')
    (hx : x ≫ f = s) (hs' : s' ≫ g = s)
    (hx' : x' ≫ f' = s') (hg' : x' ≫ g' = x)
    (F : AbelianSheaf.{u, u + 1} X) :
    pointedStalkUnit g s' ((directImage f).obj F) s hs' ≫
        (pointSmallEtale s').sheafFiber.map ((baseChangeMap f f' g g' h).app F) ≫
        pointedDirectImageEvaluation f' x' s' hx' ((inverseImage g').obj F) =
      pointedDirectImageEvaluation f x s hx F ≫ pointedStalkUnit g' x' F x hg' := by
  let H := (pointSmallEtale x').sheafFiber (A := AddCommGrpCat.{u + 1})
  let ε := (inverseImageAdjunction f).counit.app F
  have hsquare := pointedStalkUnit_square f f' g g' h x s x' s' hx hs' hx' hg'
    ((directImage f).obj F)
  have hn := pointedStalkUnit_naturality g' x' x hg' ε
  simp only [pointedDirectImageEvaluation, Category.assoc]
  rw [pointedStalkUnit_naturality_assoc f' x' s' hx'
    (L := (inverseImage g).obj ((directImage f).obj F))
    (N := (directImage f').obj ((inverseImage g').obj F))
    ((baseChangeMap f f' g g' h).app F)]
  change _ ≫ _ ≫ H.map _ ≫ H.map _ = _
  rw [← H.map_comp, baseChangeMap_counit, H.map_comp]
  have hsquare' := congrArg (fun k => k ≫ H.map ((inverseImage g').map ε)) hsquare
  simp only [Category.assoc] at hsquare'
  rw [hsquare']
  exact congrArg (fun k => pointedStalkUnit f x ((directImage f).obj F) s hx ≫ k) hn.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
