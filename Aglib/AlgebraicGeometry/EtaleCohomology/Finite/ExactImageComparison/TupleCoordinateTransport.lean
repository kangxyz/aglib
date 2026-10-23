/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.TupleCoordinateComparison

/-! # Tuple comparison through an opaque source isomorphism -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

universe v w

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
