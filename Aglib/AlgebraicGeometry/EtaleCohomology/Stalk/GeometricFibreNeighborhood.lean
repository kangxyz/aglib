/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricFibreBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage

/-! # The geometric fibre and the original pulled-back neighborhood

The canonical point of a pulled-back etale neighborhood gives the same map
from the geometric fibre along either side of the original rectangle.
Only the two defining projections of the neighborhood map are needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S') (U : S.Etale)
  (p : Over.mk (ζ ≫ g) ⟶ (Scheme.Etale.forget S).obj U)

/-- The original pointed-neighborhood rectangle commutes on the literal
geometric fibres, retaining the actual pulled-back point. -/
theorem geometricFibrePointedMap_baseChange
    (r : pullback ((siteBaseChange g).obj U).hom f' ⟶ pullback U.hom f)
    (hr₁ : r ≫ pullback.fst U.hom f =
      pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g)
    (hr₂ : r ≫ pullback.snd U.hom f = pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g') :
    (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U,
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left ≫ r =
      geometricFibreBaseChangeMap f f' g g' h ζ ≫
        (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left := by
  let v' := (geometricFibrePointedMap Ω ζ f'
    { obj := (siteBaseChange g).obj U,
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left
  let v := (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left
  let σ := geometricFibreBaseChangeMap f f' g g' h ζ
  have hp : (CoefficientStalkBaseChange.pulledBackPoint g ζ U p).left ≫
      pullback.fst U.hom g = p.left :=
    CoefficientStalkBaseChange.pointedPulledBackPoint_fst g ζ (ζ ≫ g) rfl U p
  have hv'₁ : v' ≫ pullback.fst ((siteBaseChange g).obj U).hom f' =
      pullback.fst ζ f' ≫ (CoefficientStalkBaseChange.pulledBackPoint g ζ U p).left :=
    geometricFibrePointedMap_fst Ω ζ f'
      { obj := (siteBaseChange g).obj U,
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }
  have hv'₂ : v' ≫ pullback.snd ((siteBaseChange g).obj U).hom f' = pullback.snd ζ f' :=
    geometricFibrePointedMap_snd Ω ζ f'
      { obj := (siteBaseChange g).obj U,
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }
  have hv₁ : v ≫ pullback.fst U.hom f = pullback.fst (ζ ≫ g) f ≫ p.left :=
    geometricFibrePointedMap_fst Ω (ζ ≫ g) f { obj := U, val := p }
  have hv₂ : v ≫ pullback.snd U.hom f = pullback.snd (ζ ≫ g) f :=
    geometricFibrePointedMap_snd Ω (ζ ≫ g) f { obj := U, val := p }
  have hσ₁ : σ ≫ pullback.fst (ζ ≫ g) f = pullback.fst ζ f' :=
    geometricFibreBaseChangeMap_fst f f' g g' h ζ
  have hσ₂ : σ ≫ pullback.snd (ζ ≫ g) f = pullback.snd ζ f' ≫ g' :=
    geometricFibreBaseChangeMap_snd f f' g g' h ζ
  change v' ≫ r = σ ≫ v
  apply pullback.hom_ext
  · calc
      (v' ≫ r) ≫ pullback.fst U.hom f =
          v' ≫ (r ≫ pullback.fst U.hom f) := Category.assoc _ _ _
      _ = v' ≫ (pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g) :=
        congrArg (fun k => v' ≫ k) hr₁
      _ = (v' ≫ pullback.fst ((siteBaseChange g).obj U).hom f') ≫ pullback.fst U.hom g :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst ζ f' ≫
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p).left) ≫
            pullback.fst U.hom g :=
        congrArg (fun k => k ≫ pullback.fst U.hom g) hv'₁
      _ = pullback.fst ζ f' ≫ p.left := by rw [Category.assoc, hp]
      _ = (σ ≫ pullback.fst (ζ ≫ g) f) ≫ p.left :=
        congrArg (fun k => k ≫ p.left) hσ₁.symm
      _ = σ ≫ (pullback.fst (ζ ≫ g) f ≫ p.left) := Category.assoc _ _ _
      _ = σ ≫ (v ≫ pullback.fst U.hom f) := congrArg (fun k => σ ≫ k) hv₁.symm
      _ = (σ ≫ v) ≫ pullback.fst U.hom f := (Category.assoc _ _ _).symm
  · calc
      (v' ≫ r) ≫ pullback.snd U.hom f =
          v' ≫ (r ≫ pullback.snd U.hom f) := Category.assoc _ _ _
      _ = v' ≫ (pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g') :=
        congrArg (fun k => v' ≫ k) hr₂
      _ = (v' ≫ pullback.snd ((siteBaseChange g).obj U).hom f') ≫ g' := (Category.assoc _ _ _).symm
      _ = pullback.snd ζ f' ≫ g' := congrArg (fun k => k ≫ g') hv'₂
      _ = σ ≫ pullback.snd (ζ ≫ g) f := hσ₂.symm
      _ = σ ≫ (v ≫ pullback.snd U.hom f) := congrArg (fun k => σ ≫ k) hv₂.symm
      _ = (σ ≫ v) ≫ pullback.snd U.hom f := (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
