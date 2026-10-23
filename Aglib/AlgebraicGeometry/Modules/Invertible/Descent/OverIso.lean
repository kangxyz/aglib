/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Descent.Square
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Original line-bundle lifting through an actual over-isomorphism -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- A fibre isomorphism in the commuting square transports actual lifting
of every original fibre bundle. The ambient map need not be an isomorphism. -/
theorem exists_lineBundle_lift_of_square_fiberIso
    {X Z K L : Scheme.{u}} (a : X ⟶ Z) (i : K ⟶ X) (j : L ⟶ Z)
    (e : K ≅ L) (h : i ≫ a = e.hom ≫ j)
    (hlift : ∀ C : LineBundle L, ∃ V : LineBundle Z,
      Nonempty ((pullback j).obj V.val ≅ C.val)) (C : LineBundle K) :
    ∃ W : LineBundle X, Nonempty ((pullback i).obj W.val ≅ C.val) := by
  obtain ⟨W, ⟨d⟩⟩ := exists_lineBundle_pullback_of_square a i j e.hom h hlift
    (pullbackLineBundle e.inv C)
  refine ⟨W, ⟨d ≪≫ (pullbackComp e.hom e.inv).app C.val ≪≫ ?_⟩⟩
  exact (pullbackCongr e.hom_inv_id).app C.val ≪≫ (pullbackId K).app C.val

/-- The actual base change of an over-isomorphism transports the original
line-bundle lifting property, including its original pullback isomorphism. -/
theorem exists_lineBundle_lift_of_overIso
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (r : T ⟶ S)
    (e : Over.mk f ≅ Over.mk g)
    (hlift : ∀ C : LineBundle (Limits.pullback f r), ∃ V : LineBundle X,
      Nonempty ((pullback (Limits.pullback.fst f r)).obj V.val ≅ C.val))
    (C : LineBundle (Limits.pullback g r)) :
    ∃ W : LineBundle Y,
      Nonempty ((pullback (Limits.pullback.fst g r)).obj W.val ≅ C.val) := by
  let E : Limits.pullback g r ≅ Limits.pullback f r :=
    (Over.forget T).mapIso ((Over.pullback r).mapIso e.symm)
  have h : Limits.pullback.fst g r ≫ e.inv.left = E.hom ≫ Limits.pullback.fst f r := by
    change _ = ((Over.pullback r).map e.inv).left ≫ _
    exact (Limits.pullback.lift_fst _ _ _).symm
  exact exists_lineBundle_lift_of_square_fiberIso e.inv.left
    (Limits.pullback.fst g r) (Limits.pullback.fst f r) E h hlift C

end AlgebraicGeometry.Scheme.Modules.Invertible
