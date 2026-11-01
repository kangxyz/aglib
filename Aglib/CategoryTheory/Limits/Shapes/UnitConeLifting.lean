/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Lifting through an original limiting Hom cone

The specified cone and diagram comparison retain the whole original family of
maps. No alternative limit object is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u vJ uJ

variable {C : Type u} [Category.{v} C] {J : Type uJ} [Category.{vJ} J]
  {M N : C} {F G : J ⥤ C}
  (η : (Functor.const J).obj N ⟶ G)
  (h : IsLimit ((coyoneda.obj (op M)).mapCone (⟨N, η⟩ : Cone G)))
  (e : G ≅ F)

/-- Lift the original compatible family, preserving its complete cone equation. -/
def homConeLiftData (p : (Functor.const J).obj M ⟶ F) :
    { a : M ⟶ N // (Functor.const J).map a ≫ η ≫ e.hom = p } := by
  let s := p ≫ e.inv
  have hs : (fun j => s.app j) ∈ (G ⋙ coyoneda.obj (op M)).sections := by
    intro j k f
    change s.app j ≫ G.map f = s.app k
    have hh : s.app j ≫ G.map f = (𝟙 M) ≫ s.app k := (s.naturality f).symm
    exact hh.trans (Category.id_comp (s.app k))
  let a := (Types.isLimitEquivSections h).symm ⟨fun j => s.app j, hs⟩
  have ha : (Functor.const J).map a ≫ η = s := by
    apply NatTrans.ext
    funext j
    exact congrArg (fun t => t.val j) ((Types.isLimitEquivSections h).apply_symm_apply
      ⟨fun j => s.app j, hs⟩)
  refine ⟨a, ?_⟩
  rw [← Category.assoc, ha]
  simp only [s, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include h in
/-- The same original cone components detect morphisms after the given comparison. -/
theorem homCone_maps_injective {a b : M ⟶ N}
    (hab : ∀ j, a ≫ (η ≫ e.hom).app j = b ≫ (η ≫ e.hom).app j) : a = b := by
  apply (Types.isLimitEquivSections h).injective
  ext j
  change a ≫ η.app j = b ≫ η.app j
  apply (cancel_mono (e.hom.app j)).mp
  simpa only [NatTrans.comp_app, Category.assoc] using hab j

end CategoryTheory.Limits
