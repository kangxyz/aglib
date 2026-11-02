/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Opposites

/-! # The actual iterated-slice unit on a functor into a slice

Whiskering the original iterated-slice unit through post and forget compares
the two original base diagrams. Opposite, inverse and coefficient whiskering
then give the complete coefficient comparison, including its naturality.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Over

open Opposite

universe u v a b c d

variable {C : Type u} [Category.{v} C] {X : C}
  {D : Type a} [Category.{b} D] (F : D ⥤ Over X) (W : D)

/-- The whole original iterated-slice unit, through the actual post and forget functors. -/
def postIteratedSliceBaseIso :
    Over.forget W ⋙ F ≅
      (Over.post F ⋙ Over.iteratedSliceForward (F.obj W)) ⋙ Over.map (F.obj W).hom :=
  Functor.isoWhiskerLeft (Over.post (X := W) F)
    (Functor.isoWhiskerRight (Over.iteratedSliceEquiv (F.obj W)).unitIso
      (Over.forget (F.obj W)))

/-- Each component is the original identity-underlying isomorphism and base-arrow equation. -/
theorem postIteratedSliceBaseIso_app (T : Over W) :
    (postIteratedSliceBaseIso F W).app T =
      Over.isoMk (f := F.obj T.left)
        (g := (Over.map (F.obj W).hom).obj
          ((Over.post F ⋙ Over.iteratedSliceForward (F.obj W)).obj T))
        (Iso.refl _) (by
          change (𝟙 ((F.obj T.left).left)) ≫
            ((F.map T.hom).left ≫ (F.obj W).hom) = (F.obj T.left).hom
          simpa only [Category.id_comp] using Over.w (F.map T.hom)) := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  rfl

variable {A : Type c} [Category.{d} A] (P : (Over X)ᵒᵖ ⥤ A)

/-- Opposite and inverse of the actual base comparison, evaluated by the original coefficients. -/
def postIteratedSliceCoefficientIso :
    (Over.forget W).op ⋙ (F.op ⋙ P) ≅
      (Over.post F ⋙ Over.iteratedSliceForward (F.obj W)).op ⋙
        ((Over.map (F.obj W).hom).op ⋙ P) :=
  Functor.isoWhiskerRight (NatIso.op (postIteratedSliceBaseIso F W)).symm P

/-- The whole coefficient comparison retains the original inverse/opposite component. -/
theorem postIteratedSliceCoefficientIso_app (T : Over W) :
    (postIteratedSliceCoefficientIso F W P).app (op T) =
      P.mapIso ((postIteratedSliceBaseIso F W).app T).op.symm := rfl

end CategoryTheory.Over
