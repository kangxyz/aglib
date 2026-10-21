/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSectionIso

/-! # Original restriction maps of affine coproduct sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {X : Scheme.{max u v}} {δ : Type v} [DecidableEq δ]
  (M : δ → X.Modules) [∀ i, (M i).IsQuasicoherent]

/-- The inverse affine section comparison sends each direct-sum generator to
its original ambient coproduct inclusion. -/
theorem affineOpenSectionsCoproductIso_inv_of (U : X.affineOpens)
    (i : δ) (x : Γ(M i, U.val)) :
    (affineOpenSectionsCoproductIso M U).inv
        (DirectSum.of (fun i => Γ(M i, U.val)) i x) =
      (Sigma.ι M i).app U.val x := by
  have hx := ConcreteCategory.congr_hom (affineOpenSectionsCoproductIso_ι M U i) x
  change (affineOpenSectionsCoproductIso M U).hom ((Sigma.ι M i).app U.val x) =
    DirectSum.of (fun i => Γ(M i, U.val)) i x at hx
  rw [← hx]
  exact ConcreteCategory.congr_hom (affineOpenSectionsCoproductIso M U).hom_inv_id _

/-- Under the actual affine coproduct section comparisons, restriction is the
direct sum of the original coefficient restriction maps. The coordinate-ring
actions remain those of the original sections on the two affine opens. -/
theorem affineOpenSectionsCoproductIso_inv_restriction
    (U V : X.affineOpens) (h : V.val ≤ U.val)
    (x : ⨁ i, Γ(M i, U.val)) :
    (∐ M).presheaf.map (homOfLE h).op
        ((affineOpenSectionsCoproductIso M U).inv x) =
      (affineOpenSectionsCoproductIso M V).inv
        (DirectSum.map (fun i => ((M i).presheaf.map (homOfLE h).op).hom) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i x =>
    simp only [DirectSum.map_of]
    erw [affineOpenSectionsCoproductIso_inv_of M U i x,
      affineOpenSectionsCoproductIso_inv_of M V i
        (((M i).presheaf.map (homOfLE h).op) x)]
    exact (CategoryTheory.congr_fun
      ((Sigma.ι M i).mapPresheaf.naturality (homOfLE h).op) x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The original coproduct restriction evaluated on a single homogeneous section. -/
theorem affineOpenSectionsCoproductIso_inv_restriction_of
    (U V : X.affineOpens) (h : V.val ≤ U.val) (i : δ) (x : Γ(M i, U.val)) :
    (∐ M).presheaf.map (homOfLE h).op
        ((affineOpenSectionsCoproductIso M U).inv
          (DirectSum.of (fun j => Γ(M j, U.val)) i x)) =
      (affineOpenSectionsCoproductIso M V).inv
        (DirectSum.of (fun j => Γ(M j, V.val)) i
          ((M i).presheaf.map (homOfLE h).op x)) := by
  rw [affineOpenSectionsCoproductIso_inv_restriction, DirectSum.map_of]

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
