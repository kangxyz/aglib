/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Surjectivity of locally quasi-finite morphisms from the local dimension

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes with closed image, where `Y` is
irreducible. If a point `x : X` satisfies `dim 𝒪_{Y, f x} ≤ dim 𝒪_{X, x} < ∞`, then `f` is
surjective:
`Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top`.
In particular, a locally quasi-finite endomorphism with closed image of an irreducible locally
Noetherian scheme that fixes a point is surjective
(`Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq`).

The proof uses the specialization order of schemes (Mathlib's `Scheme` preorder, `x ≤ y` when
`y ⤳ x`). The fibres of `f` are discrete (Mathlib's `Scheme.Hom.isDiscrete_preimage_singleton`),
so `f` is strictly monotone (`Scheme.Hom.strictMono_of_locallyQuasiFinite`), and
`dim 𝒪_{X, x}` is the coheight of `x` (Mathlib's `ringKrullDim_stalk_eq_coheight`). A longest
chain of generalizations of `x` maps to a chain of generalizations of `f x` in the image of `f`;
if `f` is not surjective, the generic point of `Y` is not in the closed image and lengthens that
chain by one. No bound on the dimension of `X` or `Y` is used, only the finite local dimension at
`x`, which holds at every point of a locally Noetherian scheme (Noetherian local rings have
finite Krull dimension, Mathlib's `KrullsHeightTheorem`).
-/

@[expose] public section

open CategoryTheory Order Topology

universe u

namespace AlgebraicGeometry

/-- A strictly monotone map whose values all lie strictly below a fixed element raises every
finite coheight. -/
private theorem coheight_lt_coheight_apply_of_strictMono_of_forall_lt {α β : Type*} [Preorder α]
    [Preorder β] (f : α → β) (hf : StrictMono f) {b : β} (hb : ∀ a, f a < b) {x : α}
    (hx : coheight x < ⊤) : coheight x < coheight (f x) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hx.ne
  obtain ⟨p, hp, hl⟩ := exists_series_of_le_coheight x hm.le
  let q := (p.map f hf).snoc b (hb p.last)
  have hq : q.head = f x := (RelSeries.head_snoc _ _ _).trans (congrArg f hp)
  have hlen : q.length = m + 1 := (RelSeries.snoc_length _ _ _).trans (congrArg (· + 1) hl)
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ coheight (f x) := by
    rw [← hlen, ← hq]
    exact length_le_coheight_head
  calc coheight x = m := hm.symm
    _ < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self m
    _ ≤ coheight (f x) := h1

/-- **A locally quasi-finite morphism is strictly monotone for the specialization order**: its
fibres are discrete, so it maps a strict generalization to a strict generalization. -/
theorem Scheme.Hom.strictMono_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : StrictMono f := by
  intro x y hxy
  have hyx : y ⤳ x := Scheme.le_iff_specializes.mp hxy.le
  refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hyx.map f.continuous)) fun h =>
    hxy.not_ge ?_
  have he : f x = f y :=
    (Specializes.antisymm (Scheme.le_iff_specializes.mp h) (hyx.map f.continuous)).eq
  have : DiscreteTopology (f ⁻¹' {f x}) := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hsub : (⟨y, he.symm⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ :=
    (subtype_specializes_iff (p := fun z => z ∈ f ⁻¹' {f x}) _ _).mpr hyx
  exact le_of_eq (congrArg Subtype.val hsub.eq)

namespace Scheme.Hom

/-- **Surjectivity from the local dimension.** Let `f : X ⟶ Y` be a locally quasi-finite morphism
of schemes with closed image, where `Y` is irreducible. If a point `x : X` satisfies
`dim 𝒪_{Y, f x} ≤ dim 𝒪_{X, x} < ∞`, then `f` is surjective. -/
theorem surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [IrreducibleSpace Y]
    (hf : IsClosed (Set.range f)) (x : X)
    (hle : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : ringKrullDim (X.presheaf.stalk x) < ⊤) : Surjective f := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at hle
  rw [ringKrullDim_stalk_eq_coheight] at hfin
  have hle' : coheight (f x) ≤ coheight x := by exact_mod_cast hle
  have hfin' : coheight x < ⊤ := by
    rw [← WithBot.coe_lt_coe, WithBot.coe_top]
    exact hfin
  have hrange : genericPoint Y ∈ Set.range f → Set.range f = Set.univ := fun hη => by
    have h1 : closure {genericPoint Y} ⊆ Set.range f :=
      hf.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
    rw [(genericPoint_spec Y).def] at h1
    exact Set.eq_univ_of_univ_subset h1
  constructor
  by_contra hns
  have hη : genericPoint Y ∉ Set.range f := fun hη => hns (Set.range_eq_univ.mp (hrange hη))
  have hlt : ∀ a : X, f a < genericPoint Y := fun a =>
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (genericPoint_specializes (f a))) fun h =>
      hη (hf.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨a, rfl⟩)
        (specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp h)))
  exact (coheight_lt_coheight_apply_of_strictMono_of_forall_lt f f.strictMono_of_locallyQuasiFinite
    hlt hfin').not_ge hle'

end Scheme.Hom

/-- **A locally quasi-finite endomorphism with closed image of an irreducible locally Noetherian
scheme that fixes a point is surjective.** The local ring at the fixed point is Noetherian, hence
of finite dimension. -/
theorem Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq
    {X : Scheme.{u}} (f : X ⟶ X) [LocallyQuasiFinite f] [IrreducibleSpace X] [IsLocallyNoetherian X]
    (hf : IsClosed (Set.range f)) {x : X} (hx : f x = x) : Surjective f :=
  f.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top hf x
    (by rw [hx]) ringKrullDim_lt_top

end AlgebraicGeometry
