/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The original coproduct in a slice

The coproduct of objects over a base is canonically the coproduct of their
underlying objects with the original `Sigma.desc` structure map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over

universe u v w

variable {C : Type u} [Category.{v} C] {X : C} {ι : Type w}
  (U : ι → Over X) [HasCoproduct (fun i => (U i).left)]

/-- The actual coproduct cocone with its original structure map to the base. -/
def coproductCofan : Cofan U :=
  Cofan.mk (Over.mk (Sigma.desc (fun i => (U i).hom)))
    (fun i => Over.homMk (Sigma.ι (fun j => (U j).left) i) (by simp))

/-- The original coproduct universal property, now in the slice. -/
def coproductCofanIsColimit : IsColimit (coproductCofan U) := by
  refine Cofan.IsColimit.mk _ (fun s => Over.homMk
    (Sigma.desc (fun i => (s.inj i).left)) ?_) ?_ ?_
  · apply Sigma.hom_ext
    intro i
    change Sigma.ι _ i ≫ (Sigma.desc (fun j => (s.inj j).left) ≫ s.pt.hom) =
      Sigma.ι _ i ≫ Sigma.desc (fun j => (U j).hom)
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact Over.w (s.inj i)
  · intro s i
    apply Over.OverMorphism.ext
    change Sigma.ι _ i ≫ Sigma.desc (fun j => (s.inj j).left) = (s.inj i).left
    exact Sigma.ι_comp_desc _ _
  · intro s f hf
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    have hi := congrArg (fun g => g.left) (hf i)
    simpa [coproductCofan] using hi

/-- Identification of the native slice coproduct with the underlying coproduct,
preserving its actual map to the base. -/
def coproductIso [HasCoproduct U] :
    (∐ U) ≅ Over.mk (Sigma.desc (fun i => (U i).hom)) :=
  (coproductIsCoproduct U).coconePointUniqueUpToIso (coproductCofanIsColimit U)

end CategoryTheory.Over
