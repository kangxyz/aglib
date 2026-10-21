/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSectionRestriction

/-! # Naturality of the original affine coproduct section isomorphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The actual affine section comparison identifies a coproduct of coefficient
maps with the direct sum of their original section maps. -/
theorem affineOpenSectionsCoproductIso_inv_naturality
    {X : Scheme.{max u v}} {δ : Type v} [DecidableEq δ]
    (M N : δ → X.Modules) [∀ i, (M i).IsQuasicoherent] [∀ i, (N i).IsQuasicoherent]
    (f : ∀ i, M i ⟶ N i) (U : X.affineOpens) :
    (affineOpenSectionsCoproductIso M U).inv ≫ (Limits.Sigma.map f).val.app (op U.val) =
      ModuleCat.ofHom (DirectSum.lmap (fun i => ((f i).val.app (op U.val)).hom)) ≫
        (affineOpenSectionsCoproductIso N U).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | of i x =>
    change (Limits.Sigma.map f).app U.val
        ((affineOpenSectionsCoproductIso M U).inv (DirectSum.of _ i x)) =
      (affineOpenSectionsCoproductIso N U).inv
        (DirectSum.lmap (fun i => ((f i).val.app (op U.val)).hom) (DirectSum.of _ i x))
    rw [DirectSum.lmap_of]
    erw [affineOpenSectionsCoproductIso_inv_of M U i x,
      affineOpenSectionsCoproductIso_inv_of N U i ((f i).app U.val x)]
    exact congrArg (fun q => q.app U.val x) (Limits.Sigma.ι_map f i)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
