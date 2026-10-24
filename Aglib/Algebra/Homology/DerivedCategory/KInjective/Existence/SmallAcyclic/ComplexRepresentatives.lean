/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ObjectRepresentatives
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Small codes for complexes with bounded terms

Object representatives and shrunk morphism data give a small parameter type
for native integer cochain complexes. The code is only an indexing type;
all decoded objects and isomorphisms belong to the original native category.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Small differential data on a prescribed small family of objects. -/
structure CochainCode {I : Type w} (Q : I → C) : Type w where
  /-- The index of the chosen representative in each degree. -/
  term : ℤ → I
  /-- The encoded differential between the chosen representatives. -/
  differential : ∀ i j : ℤ, Shrink.{w} (Q (term i) ⟶ Q (term j))
  shape : ∀ i j, ¬ (ComplexShape.up ℤ).Rel i j →
    (equivShrink.{w} (Q (term i) ⟶ Q (term j))).symm (differential i j) = 0
  square_zero : ∀ i j k,
    (equivShrink.{w} (Q (term i) ⟶ Q (term j))).symm (differential i j) ≫
      (equivShrink.{w} (Q (term j) ⟶ Q (term k))).symm (differential j k) = 0

namespace CochainCode

variable {I : Type w} {Q : I → C}

/-- Decode the small data into a native cochain complex. -/
def complex (a : CochainCode Q) : CochainComplex C ℤ where
  X i := Q (a.term i)
  d i j := (equivShrink.{w} _).symm (a.differential i j)
  shape := a.shape
  d_comp_d' i j k _ _ := a.square_zero i j k

/-- Encode a complex after choosing representatives for its terms. -/
def ofTermIso (K : CochainComplex C ℤ) (x : ℤ → I) (e : ∀ i, K.X i ≅ Q (x i)) :
    CochainCode Q where
  term := x
  differential i j := equivShrink.{w} _ ((e i).inv ≫ K.d i j ≫ (e j).hom)
  shape i j hij := by simp [K.shape i j hij]
  square_zero i j k := by simp [Category.assoc]

/-- The encoding preserves the entire native complex, not only its terms. -/
def isoOfTermIso (K : CochainComplex C ℤ) (x : ℤ → I) (e : ∀ i, K.X i ≅ Q (x i)) :
    K ≅ (ofTermIso K x e).complex :=
  HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    simp [complex, ofTermIso])

end CochainCode

variable {G : C} (hG : IsSeparator G)

include hG

/-- All complexes with bounded subobject cardinality in each term admit an
actual small family of representatives in the native complex category. -/
lemma exists_small_complex_representatives (κ : Cardinal.{w}) :
    ∃ (J : Type w) (R : J → CochainComplex C ℤ), ∀ K : CochainComplex C ℤ,
      (∀ n, Cardinal.mk (Shrink.{w} (Subobject (K.X n))) ≤ κ) →
        ∃ j : J, Nonempty (K ≅ R j) := by
  classical
  obtain ⟨I, Q, hQ⟩ := exists_small_object_representatives hG κ
  refine ⟨CochainCode Q, CochainCode.complex, ?_⟩
  intro K hK
  choose x hx using fun n ↦ hQ (K.X n) (hK n)
  let e : ∀ n, K.X n ≅ Q (x n) := fun n ↦ (hx n).some
  exact ⟨CochainCode.ofTermIso K x e, ⟨CochainCode.isoOfTermIso K x e⟩⟩

end CategoryTheory.IsGrothendieckAbelian
