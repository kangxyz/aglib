/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Basic

/-!
# Relabeling the native full-support relative-simplex complex

A bijection of the vertex sets induces the literal tuple relabeling
isomorphism of genuine cosimplicial objects and hence of their native
alternating coface-map complexes. The formula is retained on cochains.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicTopology.RelativeSimplex

section Tuples

variable {ι : Type v} {κ : Type w} {n : ℕ}

theorem equiv_supported_iff (e : ι ≃ κ) (a : Fin (n + 1) → ι) :
    Set.univ ⊆ Set.range (e ∘ a) ↔ Set.univ ⊆ Set.range a := by
  constructor
  · intro h i hi
    obtain ⟨k, hk⟩ := h (Set.mem_univ (e i))
    exact ⟨k, e.injective hk⟩
  · intro h k hk
    obtain ⟨i, rfl⟩ := e.surjective k
    obtain ⟨j, hj⟩ := h (Set.mem_univ i)
    exact ⟨j, congrArg e hj⟩

/-- Relabel every vertex of a full-support tuple by the indicated bijection. -/
def tupleReindex (e : ι ≃ κ) (a : Tuple (Set.univ : Set ι) n) :
    Tuple (Set.univ : Set κ) n :=
  ⟨e ∘ a.val, (equiv_supported_iff e a.val).mpr a.property⟩

@[simp]
theorem tupleReindex_symm (e : ι ≃ κ) (a : Tuple (Set.univ : Set ι) n) :
    tupleReindex e.symm (tupleReindex e a) = a := by
  apply Subtype.ext
  funext k
  exact e.symm_apply_apply _

end Tuples

variable {ι κ : Type v} {R : Type u} [Ring R] {n : ℕ}

/-- The scalar-linear cochain relabeling, by precomposition with the inverse
bijection on vertices. -/
def cochainReindex (e : ι ≃ κ) (n : ℕ) :
    Cochains R (Set.univ : Set ι) n →ₗ[R] Cochains R (Set.univ : Set κ) n where
  toFun x a := x (tupleReindex e.symm a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extendByZero_cochainReindex (e : ι ≃ κ)
    (x : Cochains R (Set.univ : Set ι) n) (a : Fin (n + 1) → κ) :
    extendByZero (cochainReindex e n x) a = extendByZero x (e.symm ∘ a) := by
  classical
  by_cases ha : Set.univ ⊆ Set.range a
  · have he := (equiv_supported_iff e.symm a).mpr ha
    simp only [extendByZero, dite_eq_left ha, dite_eq_left he, cochainReindex,
      LinearMap.coe_mk, AddHom.coe_mk, tupleReindex]
  · have he : ¬ Set.univ ⊆ Set.range (e.symm ∘ a) :=
      fun h => ha ((equiv_supported_iff e.symm a).mp h)
    simp only [extendByZero, dite_eq_right ha, dite_eq_right he]

/-- Actual vertex relabeling as a cosimplicial map. -/
def cosimplicialReindex (e : ι ≃ κ) :
    cosimplicial R (Set.univ : Set ι) ⟶ cosimplicial R (Set.univ : Set κ) where
  app n := ModuleCat.ofHom (cochainReindex e n.len)
  naturality {_ _} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change extendByZero x ((e.symm ∘ a.val) ∘ f.toOrderHom) =
      extendByZero (cochainReindex e _ x) (a.val ∘ f.toOrderHom)
    rw [extendByZero_cochainReindex]
    rfl

/-- The native cosimplicial isomorphism induced by a bijection of vertices. -/
def cosimplicialReindexIso (e : ι ≃ κ) :
    cosimplicial R (Set.univ : Set ι) ≅ cosimplicial R (Set.univ : Set κ) where
  hom := cosimplicialReindex e
  inv := cosimplicialReindex e.symm
  hom_inv_id := by
    ext n x
    funext a
    change x (tupleReindex e.symm (tupleReindex e a)) = x a
    rw [tupleReindex_symm]
  inv_hom_id := by
    ext n x
    funext a
    change x (tupleReindex e (tupleReindex e.symm a)) = x a
    exact congrArg x (tupleReindex_symm e.symm a)

/-- Native alternating-complex relabeling, with the actual cochain maps above. -/
def complexReindexIso (e : ι ≃ κ) :
    complex R (Set.univ : Set ι) ≅ complex R (Set.univ : Set κ) :=
  (alternatingCofaceMapComplex _).mapIso (cosimplicialReindexIso e)

@[simp]
theorem complexReindexIso_hom_f_apply (e : ι ≃ κ) (n : ℕ)
    (x : Cochains R (Set.univ : Set ι) n) (a : Tuple (Set.univ : Set κ) n) :
    (complexReindexIso (R := R) e).hom.f n x a = x (tupleReindex e.symm a) := rfl

end AlgebraicTopology.RelativeSimplex
