/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-! # Invertibility of original maps from literal finite-stalk tuple coordinates -/

@[expose] public noncomputable section

open CategoryTheory

namespace AddEquiv

/-- Scalar-free reindexing of dependent additive tuples. Its forward map is
literal precomposition with the supplied equivalence of indices. -/
def piReindex {I J : Type*} (e : I ≃ J) (F : J → Type*) [∀ j, Add (F j)] :
    (∀ j, F j) ≃+ (∀ i, F (e i)) where
  __ := (Equiv.piCongrLeft F e).symm
  map_add' _ _ := rfl

end AddEquiv

namespace CategoryTheory

universe v w

/-- Literal coordinate equations with actual component isomorphisms force the
original map to be invertible; no invertibility of that map is an input. -/
theorem isIso_of_tuple_coordinates {I J : Type w}
    {F : J → AddCommGrpCat.{v}} {G : I → AddCommGrpCat.{v}}
    {A B : AddCommGrpCat.{max v w}}
    (a : A ≅ AddCommGrpCat.of (∀ j, F j))
    (b : B ≅ AddCommGrpCat.of (∀ i, G i))
    (e : I ≃ J) (k : ∀ i, F (e i) ≅ G i) (t : A ⟶ B)
    (h : ∀ x : A, ∀ i, b.hom (t x) i = (k i).hom (a.hom x (e i))) :
    IsIso t := by
  let E : AddCommGrpCat.of (∀ j, F j) ≅ AddCommGrpCat.of (∀ i, G i) :=
    ((AddEquiv.piReindex e (fun j => F j)).trans
      (AddEquiv.piCongrRight fun i => (k i).addCommGroupIsoToAddEquiv)).toAddCommGrpIso
  have ht : t ≫ b.hom = a.hom ≫ E.hom := by
    apply ConcreteCategory.hom_ext
    intro x
    apply funext
    intro i
    exact h x i
  have : IsIso (t ≫ b.hom) := by
    rw [ht]
    infer_instance
  exact (isIso_comp_right_iff t b.hom).mp this

end CategoryTheory
