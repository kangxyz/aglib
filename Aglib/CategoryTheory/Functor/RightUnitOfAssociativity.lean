/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # A right unit from original associativity and the left identity unit

No right-unit equation is assumed: the actual associativity equation at two
identity factors and the left unit of the identity factor force it by cancellation.
-/

@[expose] public section
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B]
  (F : A ⥤ B) (Q : B ⥤ B)
  (ε : Q ≅ 𝟭 B) (κ : F ⋙ Q ≅ F) (μ : Q ⋙ Q ≅ Q)

/-- Original associativity at two identity factors forces the original right unit. -/
theorem rightUnit_of_associativity_leftUnit
    (ha : Functor.isoWhiskerRight κ Q ≪≫ κ =
      Functor.associator F Q Q ≪≫ Functor.isoWhiskerLeft F μ ≪≫ κ)
    (hl : μ = Functor.isoWhiskerRight ε Q ≪≫ Functor.leftUnitor Q) :
    κ = Functor.isoWhiskerLeft F ε ≪≫ Functor.rightUnitor F := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun e => e.hom.app K) ha
  simp only [hl, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.leftUnitor_hom_app,
    Category.id_comp] at hk
  have hk' := hk.trans (congrArg (fun t => t ≫ κ.hom.app K)
    (Category.comp_id (Q.map (ε.hom.app (F.obj K)))))
  have hm : Q.map (κ.hom.app K) = Q.map (ε.hom.app (F.obj K)) :=
    (cancel_mono (κ.hom.app K)).mp hk'
  have he := congrArg (fun t => t ≫ ε.hom.app (F.obj K)) hm
  have hκ := ε.hom.naturality (κ.hom.app K)
  have hε := ε.hom.naturality (ε.hom.app (F.obj K))
  change Q.map (κ.hom.app K) ≫ ε.hom.app (F.obj K) =
    ε.hom.app (Q.obj (F.obj K)) ≫ κ.hom.app K at hκ
  change Q.map (ε.hom.app (F.obj K)) ≫ ε.hom.app (F.obj K) =
    ε.hom.app (Q.obj (F.obj K)) ≫ ε.hom.app (F.obj K) at hε
  rw [hκ, hε] at he
  have hc := (cancel_epi (ε.hom.app (Q.obj (F.obj K)))).mp he
  change κ.hom.app K = ε.hom.app (F.obj K) ≫ 𝟙 (F.obj K)
  exact hc.trans (Category.comp_id (ε.hom.app (F.obj K))).symm

end CategoryTheory
