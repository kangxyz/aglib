/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Relative graphs on supplied cartesian charts

Restricting a relative graph along an actual cartesian source chart gives a
cartesian square of the native pullback lifts. Consequently closedness of the
relative graph can be checked on such charts above an original target open
cover. The source charts need not be definitionally chosen pullbacks.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

variable {X Y S T X' Y' : Scheme.{u}}

/-- The original cartesian chart carries the restricted structural triangle. -/
theorem relativeGraph_triangle (π : X ⟶ Y) (f : X ⟶ S) (y : Y ⟶ T) (s : S ⟶ T)
    (h : π ≫ y = f ≫ s) (a : X' ⟶ X) (b : Y' ⟶ Y) (π' : X' ⟶ Y')
    (H : IsPullback π' a b π) : π' ≫ (b ≫ y) = (a ≫ f) ≫ s := by
  rw [← Category.assoc, H.w, Category.assoc, h, ← Category.assoc]

/-- The native relative graph square is cartesian whenever the specified
source chart square is cartesian. -/
theorem isPullback_relativeGraph (π : X ⟶ Y) (f : X ⟶ S) (y : Y ⟶ T) (s : S ⟶ T)
    (h : π ≫ y = f ≫ s) (a : X' ⟶ X) (b : Y' ⟶ Y) (π' : X' ⟶ Y')
    (H : IsPullback π' a b π) :
    IsPullback
      (pullback.lift π' (a ≫ f) (relativeGraph_triangle π f y s h a b π' H)) a
      (pullback.map (b ≫ y) s y s b (𝟙 S) (𝟙 T) (by simp) (by simp))
      (pullback.lift π f h) := by
  let m := pullback.map (b ≫ y) s y s b (𝟙 S) (𝟙 T) (by simp) (by simp)
  have Hm : IsPullback (pullback.fst (b ≫ y) s) m b (pullback.fst y s) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback y s), m] using
      IsPullback.of_hasPullback (b ≫ y) s
  apply IsPullback.flip
  rw [← IsPullback.paste_vert_iff Hm.flip (by
    apply pullback.hom_ext <;> simp [m, H.w])]
  simpa using H.flip

/-- Closedness of the original relative graph is local on a target open
cover, using any supplied cartesian source charts and their actual graph maps. -/
theorem isClosedImmersion_graph_of_openCover
    (π : X ⟶ Y) (f : X ⟶ S) (y : Y ⟶ T) (s : S ⟶ T)
    (h : π ≫ y = f ≫ s) (𝒰 : Y.OpenCover.{v})
    (X' : 𝒰.I₀ → Scheme.{u}) (a : ∀ i, X' i ⟶ X) (π' : ∀ i, X' i ⟶ 𝒰.X i)
    (H : ∀ i, IsPullback (π' i) (a i) (𝒰.f i) π)
    (hq : ∀ i, IsClosedImmersion (pullback.lift (π' i) (a i ≫ f)
      (relativeGraph_triangle π f y s h (a i) (𝒰.f i) (π' i) (H i)))) :
    IsClosedImmersion (pullback.lift π f h) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Pullback.openCoverOfLeft 𝒰 y s)
  intro i
  have := hq i
  change IsClosedImmersion (pullback.snd (pullback.lift π f h)
    (pullback.map (𝒰.f i ≫ y) s y s (𝒰.f i) (𝟙 S) (𝟙 T) (by simp) (by simp)))
  rw [← (isPullback_relativeGraph π f y s h (a i) (𝒰.f i) (π' i) (H i)).flip.isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry.Scheme
