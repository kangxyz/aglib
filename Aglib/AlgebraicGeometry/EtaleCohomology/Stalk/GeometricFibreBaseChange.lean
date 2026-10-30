/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Over.PullbackMaps

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The original fibre map over one common point

The two pullback projections specify the map between the original fibres.
For a Cartesian square it is the isomorphism obtained from the pasted
pullback square. The point is kept fixed throughout the construction.
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
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [CommRing Ω] (ζ : Spec (.of Ω) ⟶ S')

/-- The actual map of fibres over the same specified point. -/
def geometricFibreBaseChangeMap : pullback ζ f' ⟶ pullback (ζ ≫ g) f :=
  pullback.map ζ f' (ζ ≫ g) f (𝟙 _) g' g (by simp) h

/-- Its first projection is the unchanged map to the point. -/
theorem geometricFibreBaseChangeMap_fst :
    geometricFibreBaseChangeMap f f' g g' h ζ ≫ pullback.fst (ζ ≫ g) f =
      pullback.fst ζ f' :=
  by simp only [geometricFibreBaseChangeMap, pullback.lift_fst, Category.comp_id]

/-- Its second projection retains the original base-change arrow g'. -/
theorem geometricFibreBaseChangeMap_snd :
    geometricFibreBaseChangeMap f f' g g' h ζ ≫ pullback.snd (ζ ≫ g) f =
      pullback.snd ζ f' ≫ g' :=
  pullback.lift_snd _ _ _

/-- Pasting the original Cartesian square with the point square proves
invertibility of this actual fibre map. -/
theorem geometricFibreBaseChangeMap_isIso (H : IsPullback g' f' f g) :
    IsIso (geometricFibreBaseChangeMap f f' g g' h ζ) :=
  pullback.isIso_map_of_isPullback f f' g g' h ζ H

/-- The same original fibre map, packaged as its proved Cartesian isomorphism. -/
def geometricFibreBaseChangeIso (H : IsPullback g' f' f g) :
    pullback ζ f' ≅ pullback (ζ ≫ g) f := by
  letI := geometricFibreBaseChangeMap_isIso f f' g g' h ζ H
  exact asIso (geometricFibreBaseChangeMap f f' g g' h ζ)

/-- Packaging the isomorphism keeps the literal original map. -/
theorem geometricFibreBaseChangeIso_hom (H : IsPullback g' f' f g) :
    (geometricFibreBaseChangeIso f f' g g' h ζ H).hom =
      geometricFibreBaseChangeMap f f' g g' h ζ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
