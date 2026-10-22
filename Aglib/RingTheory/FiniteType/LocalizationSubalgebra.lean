/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite subalgebras preserving principal localizations

A finite family of principal localizations which are finite type over the
coefficient ring is already obtained from one finitely generated subalgebra.
The subalgebra may contain any prescribed finite set. The actual localization
maps induced by its inclusion are bijective, without a Noetherian hypothesis.

This is the algebraic finite-data step in Stacks Project, Tag 01Z7.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace IsLocalization.Away

/-- A finitely generated subalgebra captures finitely many principal
localizations of finite type and any additional finite set of constants.
The comparison is the localization of the literal subalgebra inclusion. -/
theorem exists_fg_subalgebra_map_bijective
    {K : Type u} {R : Type v} [CommRing K] [CommRing R] [Algebra K R]
    {ι : Type w} [Finite ι] (r : ι → R) (s : Finset R)
    [∀ i, Algebra.FiniteType K (Localization.Away (r i))] :
    ∃ B : Subalgebra K R, B.FG ∧ (↑s : Set R) ⊆ B ∧
      ∃ hr : ∀ i, r i ∈ B, ∀ i,
        Function.Bijective (Localization.awayMap B.val.toRingHom (⟨r i, hr i⟩ : B)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose t ht using fun i =>
    (Algebra.FiniteType.out (R := K) (A := Localization.Away (r i)))
  let N := Σ i, {x : Localization.Away (r i) // x ∈ t i}
  let a : N → R := fun z => (sec (r z.1) z.2.1).1
  let q : Finset R := s ∪ Finset.univ.image r ∪ Finset.univ.image a
  let B : Subalgebra K R := Algebra.adjoin K (q : Set R)
  have hB : B.FG := ⟨q, rfl⟩
  have hs : (↑s : Set R) ⊆ B := by
    intro x hx
    exact Algebra.subset_adjoin (by simp [q, hx])
  have hr (i : ι) : r i ∈ B :=
    Algebra.subset_adjoin (by simp [q])
  have ha (z : N) : a z ∈ B :=
    Algebra.subset_adjoin (by simp [q])
  refine ⟨B, hB, hs, hr, fun i => ?_⟩
  let b : B := ⟨r i, hr i⟩
  have : Away (B.val b) (Localization.Away (r i)) := by
    change Away (r i) (Localization.Away (r i))
    infer_instance
  have : Away (B.val.toRingHom b) (Localization.Away (r i)) := by
    change Away (r i) (Localization.Away (r i))
    infer_instance
  let f : Localization.Away b →ₐ[K] Localization.Away (r i) :=
    mapₐ (Localization.Away b) (Localization.Away (r i)) B.val b
  have hinj : Function.Injective f :=
    mapₐ_injective_of_injective (f := B.val)
      (Aₚ := Localization.Away b) (Bₚ := Localization.Away (r i)) b Subtype.val_injective
  have htop : (⊤ : Subalgebra K (Localization.Away (r i))) ≤ f.range := by
    rw [← ht i]
    apply Algebra.adjoin_le
    intro x hx
    let z : N := ⟨i, ⟨x, hx⟩⟩
    let n : ℕ := (sec (r i) x).2
    let y : Localization.Away b :=
      IsLocalization.mk' _ (⟨a z, ha z⟩ : B)
        (⟨b ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers b)
    refine (AlgHom.mem_range f).mpr ⟨y, ?_⟩
    change map (Localization.Away b) (Localization.Away (r i)) B.val.toRingHom b y = x
    rw [map, IsLocalization.map_mk']
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    simpa [a, z, b, n] using (sec_spec (r i) x).symm
  have hsurj : Function.Surjective f := by
    intro x
    exact (AlgHom.mem_range f).mp (htop (by trivial))
  exact ⟨hinj, hsurj⟩

end IsLocalization.Away
