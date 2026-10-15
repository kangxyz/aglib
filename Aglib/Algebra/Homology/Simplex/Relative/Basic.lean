/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# The native relative-simplex alternating tuple complex

For a set `S` of vertices, degree-`n` cochains are functions on tuples of
`n + 1` vertices whose range contains `S`. Extending a cochain by zero to all
tuples gives an actual cosimplicial module object: a map of finite ordinals
acts by precomposition followed by this zero extension. Its native alternating
coface-map complex has the literal signed deletion differential.

For `S = Set.univ`, the allowed tuples are exactly the surjective tuples.
No order, cardinality, field, or nonemptiness hypothesis is imposed here.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type v}

/-- A tuple whose range contains the prescribed set of vertices. -/
abbrev Tuple (S : Set ι) (n : ℕ) :=
  {a : Fin (n + 1) → ι // S ⊆ Set.range a}

/-- Actual scalar cochains on the admissible tuples. -/
abbrev Cochains (R : Type u) (S : Set ι) (n : ℕ) := Tuple S n → R

variable {R : Type u} [Ring R] {S : Set ι} {m n p : ℕ}

/-- Extension by zero to tuples which omit a prescribed vertex. -/
def extendByZero (x : Cochains R S n) (a : Fin (n + 1) → ι) : R := by
  classical
  exact if h : S ⊆ Set.range a then x ⟨a, h⟩ else 0

@[simp]
theorem extendByZero_apply (x : Cochains R S n) (a : Tuple S n) :
    extendByZero x a.val = x a := by
  classical
  simp only [extendByZero, dite_eq_left a.property]

@[simp]
theorem extendByZero_of_not_supported (x : Cochains R S n) (a : Fin (n + 1) → ι)
    (ha : ¬ S ⊆ Set.range a) : extendByZero x a = 0 := by
  classical
  simp only [extendByZero, dite_eq_right ha]

theorem supported_of_comp {a : Fin (n + 1) → ι} {f : Fin (m + 1) → Fin (n + 1)}
    (ha : S ⊆ Set.range (a ∘ f)) : S ⊆ Set.range a := by
  rintro i hi
  obtain ⟨k, hk⟩ := ha hi
  exact ⟨f k, hk⟩

/-- The scalar-linear cochain map induced by any map of tuple positions. -/
def positionMap (f : Fin (m + 1) → Fin (n + 1)) :
    Cochains R S m →ₗ[R] Cochains R S n where
  toFun x a := extendByZero x (a.val ∘ f)
  map_add' x y := by
    classical
    ext a
    dsimp [extendByZero]
    split_ifs <;> simp
  map_smul' r x := by
    classical
    ext a
    dsimp [extendByZero]
    split_ifs <;> simp

theorem extendByZero_positionMap (f : Fin (m + 1) → Fin (n + 1))
    (x : Cochains R S m) (a : Fin (n + 1) → ι) :
    extendByZero (positionMap f x) a = extendByZero x (a ∘ f) := by
  classical
  by_cases ha : S ⊆ Set.range a
  · simp only [extendByZero, dite_eq_left ha, positionMap, LinearMap.coe_mk, AddHom.coe_mk]
  · have haf : ¬ S ⊆ Set.range (a ∘ f) := fun h => ha (supported_of_comp h)
    simp only [extendByZero, dite_eq_right ha, dite_eq_right haf]

@[simp]
theorem positionMap_id : positionMap (R := R) (S := S) (id : Fin (n + 1) → _) =
    LinearMap.id := by
  ext x a
  change extendByZero x (a.val ∘ id) = x a
  exact extendByZero_apply x a

@[simp]
theorem positionMap_comp (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (n + 1) → Fin (p + 1)) :
    (positionMap (R := R) (S := S) g).comp (positionMap f) = positionMap (g ∘ f) := by
  ext x a
  change extendByZero (positionMap f x) (a.val ∘ g) = extendByZero x (a.val ∘ (g ∘ f))
  rw [extendByZero_positionMap]
  rfl

/-- The genuine cosimplicial module of relative-simplex cochains. -/
def cosimplicial (R : Type u) [Ring R] (S : Set ι) :
    CosimplicialObject (ModuleCat.{max u v} R) where
  obj n := ModuleCat.of R (Cochains R S n.len)
  map f := ModuleCat.ofHom (positionMap f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    exact positionMap_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (positionMap_comp f.toOrderHom g.toOrderHom).symm

/-- The actual alternating coface-map complex of the displayed cosimplicial object. -/
def complex (R : Type u) [Ring R] (S : Set ι) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (alternatingCofaceMapComplex _).obj (cosimplicial R S)

@[simp]
theorem complex_X (R : Type u) [Ring R] (S : Set ι) (n : ℕ) :
    (complex R S).X n = ModuleCat.of R (Cochains R S n) := rfl

/-- Literal alternating deletion, with zero extension whenever a face omits a
required vertex. -/
theorem d_apply (x : Cochains R S n) (a : Tuple S (n + 1)) :
    (complex R S).d n (n + 1) x a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        extendByZero x (a.val ∘ j.succAbove) := by
  simp only [complex, alternatingCofaceMapComplex_obj, AlternatingCofaceMapComplex.obj,
    CochainComplex.of_d]
  simp only [AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
    (fun b : Tuple S (n + 1) => extendByZero x (b.val ∘ j.succAbove))) a = _
  simp only [Finset.sum_apply, Pi.smul_apply]

/-- Requiring every vertex is precisely surjectivity of the tuple. -/
theorem univ_supported_iff_surjective (a : Fin (n + 1) → ι) :
    Set.univ ⊆ Set.range a ↔ Function.Surjective a := by
  simp only [Set.univ_subset_iff, Set.range_eq_univ]

end AlgebraicTopology.RelativeSimplex
