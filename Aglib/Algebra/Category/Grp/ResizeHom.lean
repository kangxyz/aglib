/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.Resize

/-! # Maps out of the original resized additive diagram

This uses the existing resize object and its original map law. The component
maps are composed with the same canonical Shrink equivalence, with no new
representation of either additive diagram.
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe r e uI vI

variable {I : Type uI} [Category.{vI} I]

/-- Actual additive component maps and their original naturality produce a map from resize. -/
def resizeAdditiveDiagramHom (F : I ⥤ AddCommGrpCat.{e})
    (G : I ⥤ AddCommGrpCat.{r}) [∀ i, Small.{r} (F.obj i)]
    (α : ∀ i, F.obj i →+ G.obj i)
    (naturality : ∀ {i j : I} (a : i ⟶ j) (x : F.obj i),
      α j (F.map a x) = G.map a (α i x)) :
    resizeAdditiveDiagram.{r} F ⟶ G where
  app i := AddCommGrpCat.ofHom ((α i).comp Shrink.addEquiv.toAddMonoidHom)
  naturality i j a := by
    ext x
    change α j (Shrink.addEquiv ((resizeAdditiveDiagram.{r} F).map a x)) =
      G.map a (α i (Shrink.addEquiv x))
    have h := resizeAdditiveDiagram_map_apply.{r} F a x
    exact (congrArg (fun y : Shrink.{r} (F.obj j) => α j (Shrink.addEquiv y)) h).trans
      ((congrArg (α j) (Shrink.addEquiv.apply_symm_apply _)).trans
        (naturality a (Shrink.addEquiv x)))

end CategoryTheory
