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
  have hp : (CoefficientStalkBaseChange.pulledBackPoint g ζ U p).left ≫
      pullback.fst U.hom g = p.left :=
    CoefficientStalkBaseChange.pointedPulledBackPoint_fst g ζ (ζ ≫ g) rfl U p
  apply pullback.hom_ext
  · calc
      _ = (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U,
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left ≫
          pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g := by
        rw [Category.assoc, hr₁]
      _ = pullback.fst ζ f' ≫ p.left := by
        rw [← Category.assoc, geometricFibrePointedMap_fst, Category.assoc, hp]
      _ = _ := by
        rw [Category.assoc, geometricFibrePointedMap_fst, ← Category.assoc,
          geometricFibreBaseChangeMap_fst]
  · calc
      _ = (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U,
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left ≫
          pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g' := by
        rw [Category.assoc, hr₂]
      _ = pullback.snd ζ f' ≫ g' := by
        rw [← Category.assoc, geometricFibrePointedMap_snd]
      _ = _ := by
        rw [Category.assoc, geometricFibrePointedMap_snd, geometricFibreBaseChangeMap_snd]


end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
