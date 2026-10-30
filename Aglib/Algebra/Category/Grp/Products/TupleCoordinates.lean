/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-! # Actual additive tuple coordinates and their reindexing isomorphism -/

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

/-- The actual dependent tuple isomorphism, retaining literal precomposition
with the given index equivalence and the supplied coordinate isomorphisms. -/
def tupleCoordinateIso {I J : Type w}
    (F : J → AddCommGrpCat.{v}) (G : I → AddCommGrpCat.{v})
    (e : I ≃ J) (k : ∀ i, F (e i) ≅ G i) :
    AddCommGrpCat.of (∀ j, F j) ≅ AddCommGrpCat.of (∀ i, G i) :=
  ((AddEquiv.piReindex e (fun j => F j)).trans
    (AddEquiv.piCongrRight fun i => (k i).addCommGroupIsoToAddEquiv)).toAddCommGrpIso

@[simp]
theorem tupleCoordinateIso_hom_apply {I J : Type w}
    (F : J → AddCommGrpCat.{v}) (G : I → AddCommGrpCat.{v})
    (e : I ≃ J) (k : ∀ i, F (e i) ≅ G i) (x : ∀ j, F j) (i : I) :
    (tupleCoordinateIso F G e k).hom x i = (k i).hom (x (e i)) := rfl

/-- The literal coordinate equations determine the whole original map. -/
theorem tuple_coordinates_eq {I J : Type w}
    {F : J → AddCommGrpCat.{v}} {G : I → AddCommGrpCat.{v}}
    {A B : AddCommGrpCat.{max v w}}
    (a : A ≅ AddCommGrpCat.of (∀ j, F j))
    (b : B ≅ AddCommGrpCat.of (∀ i, G i))
    (e : I ≃ J) (k : ∀ i, F (e i) ≅ G i) (t : A ⟶ B)
    (h : ∀ x : A, ∀ i, b.hom (t x) i = (k i).hom (a.hom x (e i))) :
    t ≫ b.hom = a.hom ≫ (tupleCoordinateIso F G e k).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  funext i
  exact h x i

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
  have ht := tuple_coordinates_eq a b e k t h
  have : IsIso (t ≫ b.hom) := by
    rw [ht]
    infer_instance
  exact (isIso_comp_right_iff t b.hom).mp this

/-- Keep the source comparison opaque when applying actual tuple coordinates. -/
theorem isIso_of_tuple_coordinates_via_iso {I J : Type w}
    {F : J → AddCommGrpCat.{v}} {G : I → AddCommGrpCat.{v}}
    {A B C : AddCommGrpCat.{max v w}}
    (v : A ≅ C) (a : C ≅ AddCommGrpCat.of (∀ j, F j))
    (b : B ≅ AddCommGrpCat.of (∀ i, G i))
    (e : I ≃ J) (k : ∀ i, G i ≅ F (e i)) (t : A ⟶ B)
    (h : ∀ x : A, ∀ i, a.hom (v.hom x) (e i) = (k i).hom (b.hom (t x) i)) :
    IsIso t := by
  apply isIso_of_tuple_coordinates (v ≪≫ a) b e (fun i => (k i).symm) t
  intro x i
  change b.hom (t x) i = (k i).inv (a.hom (v.hom x) (e i))
  rw [h]
  exact (ConcreteCategory.congr_hom (k i).hom_inv_id (b.hom (t x) i)).symm

end CategoryTheory
