/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Original map lifting through epimorphic cone units

A limiting original Hom cone and epimorphic source units make an original map
assignment bijective. Its only compatibility input is the complete original
unit square. No new diagram, completion or map assignment is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u vJ uJ

variable {C : Type u} [Category.{v} C] {J : Type uJ} [Category.{vJ} J]
  {M N : C} {F G : J ⥤ C}
  (ηM : (Functor.const J).obj M ⟶ F) (ηN : (Functor.const J).obj N ⟶ G)
  (m : (M ⟶ N) → (F ⟶ G))
  (hm : ∀ a, (Functor.const J).map a ≫ ηN = ηM ≫ m a)
  (hN : IsLimit ((coyoneda.obj (op M)).mapCone (⟨N, ηN⟩ : Cone G)))
  [∀ j, Epi (ηM.app j)]

include hm hN in
/-- The original map assignment is bijective, with no additional formal-fullness premise. -/
theorem map_bijective_of_unit_homCone : Function.Bijective m := by
  have hext {a b : M ⟶ N} (h : ∀ j, a ≫ ηN.app j = b ≫ ηN.app j) : a = b := by
    apply (Types.isLimitEquivSections hN).injective
    ext j
    exact h j
  constructor
  · intro a b hab
    apply hext
    have h := (hm a).trans ((congrArg (fun t => ηM ≫ t) hab).trans (hm b).symm)
    intro j
    exact NatTrans.congr_app h j
  · intro φ
    let s := ηM ≫ φ
    have hs : (fun j => s.app j) ∈ (G ⋙ coyoneda.obj (op M)).sections := by
      intro j k f
      change s.app j ≫ G.map f = s.app k
      have h : s.app j ≫ G.map f = (𝟙 M) ≫ s.app k := (s.naturality f).symm
      exact h.trans (Category.id_comp (s.app k))
    obtain ⟨a, ha, _⟩ := (Types.isLimit_iff _).mp ⟨hN⟩ (fun j => s.app j) hs
    refine ⟨a, ?_⟩
    apply NatTrans.ext
    funext j
    apply (cancel_epi (ηM.app j)).mp
    exact (NatTrans.congr_app (hm a) j).symm.trans (ha j)

end CategoryTheory.Limits
