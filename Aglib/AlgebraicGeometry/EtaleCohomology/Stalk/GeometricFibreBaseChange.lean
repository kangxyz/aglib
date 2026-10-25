/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

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
  pullback.lift (pullback.fst ζ f') (pullback.snd ζ f' ≫ g') (by
    calc
      pullback.fst ζ f' ≫ (ζ ≫ g) = (pullback.fst ζ f' ≫ ζ) ≫ g :=
        (Category.assoc _ _ _).symm
      _ = (pullback.snd ζ f' ≫ f') ≫ g :=
        congrArg (fun k => k ≫ g) pullback.condition
      _ = pullback.snd ζ f' ≫ (f' ≫ g) := Category.assoc _ _ _
      _ = pullback.snd ζ f' ≫ (g' ≫ f) := congrArg (fun k => pullback.snd ζ f' ≫ k) h
      _ = (pullback.snd ζ f' ≫ g') ≫ f := (Category.assoc _ _ _).symm)

/-- Its first projection is the unchanged map to the point. -/
theorem geometricFibreBaseChangeMap_fst :
    geometricFibreBaseChangeMap f f' g g' h ζ ≫ pullback.fst (ζ ≫ g) f =
      pullback.fst ζ f' :=
  pullback.lift_fst _ _ _

/-- Its second projection retains the original base-change arrow g'. -/
theorem geometricFibreBaseChangeMap_snd :
    geometricFibreBaseChangeMap f f' g g' h ζ ≫ pullback.snd (ζ ≫ g) f =
      pullback.snd ζ f' ≫ g' :=
  pullback.lift_snd _ _ _

/-- Pasting the original Cartesian square with the point square proves
invertibility of this actual fibre map. -/
theorem geometricFibreBaseChangeMap_isIso (H : IsPullback g' f' f g) :
    IsIso (geometricFibreBaseChangeMap f f' g g' h ζ) := by
  have H₀ : IsPullback (pullback.fst ζ f') (pullback.snd ζ f' ≫ g') (ζ ≫ g) f :=
    ((IsPullback.of_hasPullback ζ f').flip.paste_horiz H).flip
  have heq : geometricFibreBaseChangeMap f f' g g' h ζ = H₀.isoPullback.hom := by
    apply pullback.hom_ext
    · exact (geometricFibreBaseChangeMap_fst f f' g g' h ζ).trans
        H₀.isoPullback_hom_fst.symm
    · exact (geometricFibreBaseChangeMap_snd f f' g g' h ζ).trans
        H₀.isoPullback_hom_snd.symm
  rw [heq]
  infer_instance

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
