/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-! # Changing the source of the actual pseudofunctor Hom presheaf

The original pullback of a source isomorphism induces the Hom-source
comparison on every slice object. Its naturality uses the same pullHom and
pseudofunctor composition maps as the original Hom presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

universe u v w z

/-- An actual source isomorphism induces the original pullback Hom comparison. -/
def presheafHomSourceIso {C : Type u} [Category.{v} C]
    (P : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, z}) {X : C}
    {M M' : P.obj (.mk (op X))} (e : M ≅ M') (N : P.obj (.mk (op X))) :
    P.presheafHom M N ≅ P.presheafHom M' N :=
  NatIso.ofComponents (fun T =>
    (Iso.homCongr ((P.map T.unop.hom.op.toLoc).toFunctor.mapIso e)
      (Iso.refl ((P.map T.unop.hom.op.toLoc).toFunctor.obj N))).toIso)
    (by
      intro T U f
      ext h
      dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
        Iso.homCongr, Equiv.toIso]
      simp only [Category.comp_id, Functor.map_comp, Category.assoc]
      rw [P.mapComp'_hom_naturality_assoc])

end CategoryTheory.Pseudofunctor
