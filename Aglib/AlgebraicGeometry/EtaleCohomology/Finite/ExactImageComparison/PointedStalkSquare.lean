/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientStalkBaseChange
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.SquareComparison

/-! # The original pointed stalk units respect the canonical inverse-image square -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge
open CoefficientStalkBaseChange

variable {X S X' S' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Naturality of the original pointed unit retains the specified point triangle. -/
@[reassoc]
theorem pointedStalkUnit_naturality (f : X ⟶ S) (x : Spec (.of Ω) ⟶ X)
    (s : Spec (.of Ω) ⟶ S) (hx : x ≫ f = s)
    {L N : AbelianSheaf.{u, u + 1} S} (a : L ⟶ N) :
    (pointSmallEtale s).sheafFiber.map a ≫ pointedStalkUnit f x N s hx =
      pointedStalkUnit f x L s hx ≫
        (pointSmallEtale x).sheafFiber.map ((inverseImage f).map a) := by
  subst s
  exact stalkUnit_naturality f x L a

/-- The original two pointed pullbacks commute through the actual square comparison. -/
theorem pointedStalkUnit_square
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f)
    (x : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ S)
    (x' : Spec (.of Ω) ⟶ X') (s' : Spec (.of Ω) ⟶ S')
    (hx : x ≫ f = s) (hs' : s' ≫ g = s)
    (hx' : x' ≫ f' = s') (hg' : x' ≫ g' = x)
    (L : AbelianSheaf.{u, u + 1} S) :
    (pointedStalkUnit g s' L s hs' ≫
      pointedStalkUnit f' x' ((inverseImage g).obj L) s' hx') ≫
        (pointSmallEtale x').sheafFiber.map ((inverseImageSquareIso f f' g g' h).hom.app L) =
      pointedStalkUnit f x L s hx ≫
        pointedStalkUnit g' x' ((inverseImage f).obj L) x hg' := by
  let H := (pointSmallEtale x').sheafFiber (A := AddCommGrpCat.{u + 1})
  have hl := pointedStalkUnit_comp g s' L f' x' s hx' hs'
  have hr := pointedStalkUnit_comp f x L g' x' s hg' hx
  have ht : pointedStalkUnit (f' ≫ g) x' L s
        (by rw [← Category.assoc, hx', hs']) ≫
      H.map ((eqToHom (congrArg (fun k : X' ⟶ S => inverseImage k) h)).app L) =
      pointedStalkUnit (g' ≫ f) x' L s (by rw [← Category.assoc, hg', hx]) := by
    simpa only [eqToHom_app] using
      pointedStalkUnit_congr (f' ≫ g) x' L h s
        (by rw [← Category.assoc, hx', hs']) (by rw [← Category.assoc, hg', hx])
  have hc := congr_app (inverseImageSquareIso_comp_hom f f' g g' h) L
  simp only [NatTrans.comp_app] at hc
  change (_ ≫ _) ≫ H.map _ = _
  rw [← hl, Category.assoc, ← H.map_comp, hc, H.map_comp, ← Category.assoc, ht]
  exact hr

end AlgebraicGeometry.Scheme.EtaleCohomology
