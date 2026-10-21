/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Transporting diagram laws while retaining the specified maps

A stagewise equivalence proves functor laws for a prescribed map family.
The resulting functor uses that family literally, not conjugated replacements.
Natural diagram isomorphisms act coordinatewise on the native sections submodule.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat

universe u v w w'
variable {R : Type u} [Ring R] {J : Type w} [Category.{w'} J]
  (P : J ⥤ ModuleCat.{v} R) (Q : J → ModuleCat.{v} R)
  (T : ∀ {a b : J}, (a ⟶ b) → (Q a ⟶ Q b))
  (e : ∀ a, P.obj a ≃ₗ[R] Q a)
  (h : ∀ {a b : J} (φ : a ⟶ b) (x : P.obj a), T φ (e a x) = e b (P.map φ x))

/-- A diagram with the specified object and arrow families, whose laws follow
from their compatibility with a given diagram. -/
def functorOfLinearEquiv : J ⥤ ModuleCat.{v} R where
  obj := Q
  map := T
  map_id a := by
    ext z
    obtain ⟨x, rfl⟩ := (e a).surjective z
    rw [h]
    simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply]
  map_comp {a b c} φ ψ := by
    ext z
    obtain ⟨x, rfl⟩ := (e a).surjective z
    change T (φ ≫ ψ) (e a x) = T ψ (T φ (e a x))
    rw [h, h, h, CategoryTheory.Functor.map_comp]
    rfl

/-- The stage equivalences give the original natural diagram isomorphism. -/
def functorOfLinearEquivIso : P ≅ functorOfLinearEquiv P Q T e h :=
  NatIso.ofComponents (fun a => (e a).toModuleIso) (by
    intro a b φ
    ext x
    exact (h φ x).symm)

variable {P Q T e h}

/-- A natural diagram isomorphism gives a coordinatewise equivalence of the
native compatible-family submodules. -/
def sectionsSubmoduleCongr {P Q : J ⥤ ModuleCat.{v} R} (e : P ≅ Q) :
    sectionsSubmodule P ≃ₗ[R] sectionsSubmodule Q where
  toFun s := ⟨fun a => e.hom.app a (s.val a), by
    intro a b φ
    have hn := ConcreteCategory.congr_hom (e.hom.naturality φ) (s.val a)
    simp only [ModuleCat.comp_apply] at hn
    change Q.map φ (e.hom.app a (s.val a)) = e.hom.app b (s.val b)
    exact hn.symm.trans (congrArg (e.hom.app b) (s.property φ))⟩
  invFun s := ⟨fun a => e.inv.app a (s.val a), by
    intro a b φ
    have hn := ConcreteCategory.congr_hom (e.inv.naturality φ) (s.val a)
    simp only [ModuleCat.comp_apply] at hn
    change P.map φ (e.inv.app a (s.val a)) = e.inv.app b (s.val b)
    exact hn.symm.trans (congrArg (e.inv.app b) (s.property φ))⟩
  left_inv s := by
    apply Subtype.ext
    funext a
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app a) (s.val a)
  right_inv s := by
    apply Subtype.ext
    funext a
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app a) (s.val a)
  map_add' s t := by
    apply Subtype.ext
    funext a
    exact map_add _ _ _
  map_smul' r s := by
    apply Subtype.ext
    funext a
    exact map_smul _ _ _

/-- The section equivalence has the original component arrow at every coordinate. -/
@[simp]
theorem sectionsSubmoduleCongr_apply {P Q : J ⥤ ModuleCat.{v} R} (e : P ≅ Q)
    (s : sectionsSubmodule P) (a : J) :
    (sectionsSubmoduleCongr e s).val a = e.hom.app a (s.val a) := rfl

end ModuleCat
