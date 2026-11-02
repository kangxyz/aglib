/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Original cone lifting through generators and kernel relations

A cone detected by an object also has the expected lifting property for an
object presented by coproducts of that object. The original epimorphism and
its actual kernel generators are retained; the lift descends by the native
cokernel universal property. No finite index or replacement presentation is
required.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u vD uD uI uJ

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] {F : D ⥤ C}
  (c : Cone F) (O : C)
  (hO : IsLimit ((coyoneda.obj (op O)).mapCone c))
  {M : C} {I : Type uI} {J : Type uJ}
  [HasCoproduct (fun _ : I => O)] [HasCoproduct (fun _ : J => O)]
  (p : (∐ fun _ : I => O) ⟶ M) [Epi p]
  (q : (∐ fun _ : J => O) ⟶ kernel p) [Epi q]

include hO p q in
/-- Every compatible original family uniquely lifts through the original presentation. -/
theorem existsUnique_lift_of_generators
    (s : ∀ d, M ⟶ F.obj d)
    (hs : ∀ ⦃d e⦄ (f : d ⟶ e), s d ≫ F.map f = s e) :
    ∃! a : M ⟶ c.pt, ∀ d, a ≫ c.π.app d = s d := by
  have hext {a b : O ⟶ c.pt}
      (h : ∀ d, a ≫ c.π.app d = b ≫ c.π.app d) : a = b := by
    apply (Types.isLimitEquivSections hO).injective
    ext d
    exact h d
  have hlift (i : I) : ∃ a : O ⟶ c.pt,
      ∀ d, a ≫ c.π.app d = Sigma.ι (fun _ : I => O) i ≫ p ≫ s d := by
    apply ExistsUnique.exists
    apply (Types.isLimit_iff _).mp ⟨hO⟩
    intro d e f
    change (Sigma.ι (fun _ : I => O) i ≫ p ≫ s d) ≫ F.map f = _
    simp only [Category.assoc, hs f]
  choose a ha using hlift
  let l : (∐ fun _ : I => O) ⟶ c.pt := Sigma.desc a
  have hl (d : D) : l ≫ c.π.app d = p ≫ s d := by
    apply Sigma.hom_ext
    intro i
    simpa only [l, Sigma.ι_comp_desc_assoc, Category.assoc] using ha i d
  have hk : kernel.ι p ≫ l = 0 := by
    apply (cancel_epi q).mp
    apply Sigma.hom_ext
    intro j
    apply hext
    intro d
    simp only [Category.assoc, hl d, kernel.condition_assoc, comp_zero, zero_comp]
  let aM := Abelian.epiDesc p l hk
  have haM (d : D) : aM ≫ c.π.app d = s d := by
    apply (cancel_epi p).mp
    simpa only [aM, Abelian.comp_epiDesc_assoc] using hl d
  refine ⟨aM, haM, ?_⟩
  intro b hb
  apply (cancel_epi p).mp
  apply Sigma.hom_ext
  intro i
  apply hext
  intro d
  simp only [Category.assoc, hb d, haM d]

include hO p q in
/-- The unchanged coyoneda cone is limiting for an object with these original generators. -/
theorem coyoneda_isLimit_of_generators :
    Nonempty (IsLimit ((coyoneda.obj (op M)).mapCone c)) := by
  apply (Types.isLimit_iff _).mpr
  intro s hs
  exact existsUnique_lift_of_generators c O hO p q s (fun _ _ f => hs f)

end CategoryTheory.Limits
