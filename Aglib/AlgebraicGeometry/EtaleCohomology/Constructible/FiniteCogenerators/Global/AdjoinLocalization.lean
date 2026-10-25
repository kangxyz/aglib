/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.Ring

/-! # Original generated subalgebras retain principal localization

Denominator clearing for the actual generator images extends to all algebra
expressions. Units and equality detection come from the original ambient
localization; no localization of the generated algebra is assumed.
Finite families of finite module images also give finite algebra generation.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

section Rings

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B] [Algebra R B]
  [IsScalarTower R A B] [IsScalarTower R S B]

/-- Denominator clearing for all actual algebra expressions, from denominator
clearing for their original generators. -/
theorem adjoin_clear_power (r : R) [IsLocalization.Away r S]
    (s : Set A) (t : Set B)
    (ht : ∀ x ∈ t, ∃ (n : ℕ) (a : A), a ∈ Algebra.adjoin R s ∧
      x * algebraMap R B r ^ n = algebraMap A B a)
    {x : B} (hx : x ∈ Algebra.adjoin S t) :
    ∃ (n : ℕ) (a : A), a ∈ Algebra.adjoin R s ∧
      x * algebraMap R B r ^ n = algebraMap A B a := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ht x hx
  | algebraMap a =>
      obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj r a
      refine ⟨n, algebraMap R A b, (Algebra.adjoin R s).algebraMap_mem b, ?_⟩
      have h := congrArg (algebraMap S B) hb
      simpa only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] using h
  | add x y hx hy ihx ihy =>
      obtain ⟨n, a, ha, hxa⟩ := ihx
      obtain ⟨m, b, hb, hyb⟩ := ihy
      refine ⟨n + m, a * algebraMap R A r ^ m + b * algebraMap R A r ^ n,
        (Algebra.adjoin R s).add_mem
          ((Algebra.adjoin R s).mul_mem ha
            ((Algebra.adjoin R s).pow_mem ((Algebra.adjoin R s).algebraMap_mem r) m))
          ((Algebra.adjoin R s).mul_mem hb
            ((Algebra.adjoin R s).pow_mem ((Algebra.adjoin R s).algebraMap_mem r) n)), ?_⟩
      calc
        (x + y) * algebraMap R B r ^ (n + m) =
            (x * algebraMap R B r ^ n) * algebraMap R B r ^ m +
              (y * algebraMap R B r ^ m) * algebraMap R B r ^ n := by
          rw [pow_add]
          ring
        _ = algebraMap A B a * algebraMap R B r ^ m +
            algebraMap A B b * algebraMap R B r ^ n := by rw [hxa, hyb]
        _ = algebraMap A B
            (a * algebraMap R A r ^ m + b * algebraMap R A r ^ n) := by
          simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  | mul x y hx hy ihx ihy =>
      obtain ⟨n, a, ha, hxa⟩ := ihx
      obtain ⟨m, b, hb, hyb⟩ := ihy
      refine ⟨n + m, a * b, (Algebra.adjoin R s).mul_mem ha hb, ?_⟩
      calc
        (x * y) * algebraMap R B r ^ (n + m) =
            (x * algebraMap R B r ^ n) * (y * algebraMap R B r ^ m) := by
          rw [pow_add]
          ring
        _ = algebraMap A B (a * b) := by rw [hxa, hyb, map_mul]

/-- The original ambient algebra map restricted to the generated subalgebras. -/
def adjoinMap (s : Set A) (t : Set B)
    (hs : ∀ x ∈ s, algebraMap A B x ∈ Algebra.adjoin S t) :
    Algebra.adjoin R s →+* Algebra.adjoin S t := by
  have hm (a : A) (ha : a ∈ Algebra.adjoin R s) :
      algebraMap A B a ∈ Algebra.adjoin S t := by
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x =>
        rw [← IsScalarTower.algebraMap_apply R A B,
          IsScalarTower.algebraMap_apply R S B]
        exact (Algebra.adjoin S t).algebraMap_mem (algebraMap R S x)
    | add x y hx hy ihx ihy =>
        rw [map_add]
        exact (Algebra.adjoin S t).add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact (Algebra.adjoin S t).mul_mem ihx ihy
  exact {
    toFun := fun a => ⟨algebraMap A B a.1, hm a.1 a.2⟩
    map_one' := Subtype.ext (map_one (algebraMap A B))
    map_mul' := fun a b => Subtype.ext (map_mul (algebraMap A B) (a : A) (b : A))
    map_zero' := Subtype.ext (map_zero (algebraMap A B))
    map_add' := fun a b => Subtype.ext (map_add (algebraMap A B) (a : A) (b : A)) }

/-- Generated subalgebras retain the original ambient localization as soon as
localized generators clear their original denominators. -/
theorem adjoin_isLocalization (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R A r) B] (s : Set A) (t : Set B)
    (hs : ∀ x ∈ s, algebraMap A B x ∈ Algebra.adjoin S t)
    (ht : ∀ x ∈ t, ∃ (n : ℕ) (a : A), a ∈ Algebra.adjoin R s ∧
      x * algebraMap R B r ^ n = algebraMap A B a) :
    letI := (adjoinMap R S A B s t hs).toAlgebra
    IsLocalization.Away (algebraMap R (Algebra.adjoin R s) r) (Algebra.adjoin S t) := by
  let φ := adjoinMap R S A B s t hs
  let := φ.toAlgebra
  have hscalar : φ (algebraMap R (Algebra.adjoin R s) r) =
      algebraMap S (Algebra.adjoin S t) (algebraMap R S r) := by
    apply Subtype.ext
    change algebraMap A B (algebraMap R A r) =
      algebraMap S B (algebraMap R S r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  apply IsLocalization.Away.mk
  · change IsUnit (φ (algebraMap R (Algebra.adjoin R s) r))
    rw [hscalar]
    exact (IsLocalization.Away.algebraMap_isUnit (S := S) r).map
      (algebraMap S (Algebra.adjoin S t))
  · intro x
    obtain ⟨n, a, ha, h⟩ := adjoin_clear_power R S A B r s t ht x.2
    refine ⟨n, ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change x.1 * algebraMap A B (algebraMap R A r) ^ n = algebraMap A B a
    simpa only [← IsScalarTower.algebraMap_apply] using h
  · intro a b h
    have hval : algebraMap A B a.1 = algebraMap A B b.1 := congrArg Subtype.val h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R A r) hval
    refine ⟨n, Subtype.ext ?_⟩
    exact hn

/-- A finitely generated module span gives finite algebra generation, with
the same original set and actual adjoin. -/
theorem adjoin_finiteType_of_span_fg (s : Set A) (h : (Submodule.span R s).FG) :
    Algebra.FiniteType R (Algebra.adjoin R s) := by
  obtain ⟨t, ht⟩ := h
  apply (Subalgebra.fg_iff_finiteType _).mp
  refine ⟨t, ?_⟩
  calc
    Algebra.adjoin R (t : Set A) =
        Algebra.adjoin R (Submodule.span R (t : Set A) : Set A) :=
      (Algebra.adjoin_span (R := R) (s := (t : Set A))).symm
    _ = Algebra.adjoin R (Submodule.span R s : Set A) := by rw [ht]
    _ = Algebra.adjoin R s := Algebra.adjoin_span R

/-- Finite families of finite module images generate actual finite-type
subalgebras of the original ambient algebra. -/
theorem adjoin_iUnion_range_finiteType {J : Type u} [Finite J]
    (M : J → Type u) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    [∀ j, Module.Finite R (M j)] (i : ∀ j, M j →ₗ[R] A) :
    Algebra.FiniteType R (Algebra.adjoin R (⋃ j, Set.range (i j))) := by
  apply adjoin_finiteType_of_span_fg R A
  have hspan : Submodule.span R (⋃ j, Set.range (i j)) = ⨆ j, (i j).range := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact le_iSup (fun j => (i j).range) j hj
    · apply iSup_le
      intro j x hx
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, hx⟩)
  rw [hspan]
  exact Submodule.fg_iSup (fun j => (i j).range) (fun j => Submodule.fg_range (i j))

end Rings

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
