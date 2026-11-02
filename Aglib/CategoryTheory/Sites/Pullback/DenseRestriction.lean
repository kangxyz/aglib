/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Faithfulness of the original cover-dense coefficient restriction

The actual underlying target sheaf detects equality using cover density.
Local fullness and a replacement inverse-image functor are not required.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

universe c₁ h₁ c₂ h₂ w

variable {C : Type c₁} [Category.{h₁} C] {D : Type c₂} [Category.{h₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCoverDense K]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]

/-- The same continuous restriction on additive sheaves is faithful under
cover density, with no local-fullness assumption. -/
theorem sheafPushforwardContinuous_faithful_of_isCoverDense :
    (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Faithful where
  map_injective {P Q} α β h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply Functor.IsCoverDense.ext F
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).obj Q) U.unop
    intro V a
    have ha := congrArg (fun z => z.hom.app (op V)) h
    change α.hom.app (op (F.obj V)) = β.hom.app (op (F.obj V)) at ha
    exact (ConcreteCategory.congr_hom (α.hom.naturality a.op) x).symm.trans
      ((congrArg (fun z => z (P.obj.map a.op x)) ha).trans
        (ConcreteCategory.congr_hom (β.hom.naturality a.op) x))

end CategoryTheory.Functor
