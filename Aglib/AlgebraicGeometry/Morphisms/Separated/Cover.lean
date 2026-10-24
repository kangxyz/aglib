/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Separatedness from a cover by separated opens

Let `f : P ⟶ S` be a morphism of schemes and `(U_i)` opens covering `P`, each with `U_i ⟶ S`
separated, such that any two of them are disjoint or both contained in a third. Then `f` is
separated (`isSeparated_of_cover_of_disjoint_or_le`). Special cases are a cover by pairwise
disjoint separated opens (`isSeparated_of_cover_of_pairwise_disjoint`), a directed cover by
separated opens, for example an increasing union (`isSeparated_of_cover_of_directed`), and a
cover `U i m` disjoint for distinct `i` and increasing in `m` for a directed order
(`isSeparated_of_cover_of_disjoint_of_monotone`).

Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 28: "Plainly an
`S`-scheme is separated if it is a disjoint union of separated open subschemes, or if it is an
increasing union of separated open subschemes." The mixed condition contains both cases. It is
the form needed for a cover whose members are disjoint for distinct indices of one kind and
nested in another index.

Proof. The diagonal of `f` is an immersion, so it is a closed immersion once its range is closed.
Let `z ∈ P ×_S P` be off the diagonal, with `pr₁ z ∈ U_i` and `pr₂ z ∈ U_j`. If `U_i` and `U_j`
are disjoint, the open `pr₁⁻¹ U_i ∩ pr₂⁻¹ U_j` misses the diagonal. If both lie in `U_k`, then
`z` lies in the range of the open immersion `m : U_k ×_S U_k ⟶ P ×_S P`, whose range is
`pr₁⁻¹ U_k ∩ pr₂⁻¹ U_k` (`Scheme.Pullback.range_map`), and `m` carries the diagonal of `U_k` into
that of `P`; the image under `m` of the complement of the closed diagonal of `U_k` is an open
neighbourhood of `z` missing the diagonal of `P`
(`exists_isOpen_subset_compl_range_diagonal`). No finiteness or Noetherian hypothesis is used.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {P S : Scheme.{u}}

/-- The first projection of the diagonal point `Δ(x)` is `x`. -/
theorem pullback_fst_diagonal_apply (f : P ⟶ S) (x : P) :
    pullback.fst f f (pullback.diagonal f x) = x := by
  rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
  rfl

/-- The second projection of the diagonal point `Δ(x)` is `x`. -/
theorem pullback_snd_diagonal_apply (f : P ⟶ S) (x : P) :
    pullback.snd f f (pullback.diagonal f x) = x := by
  rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
  rfl

/-- The nested case, for an arbitrary open immersion `m` of a fibre product into `P ×_S P`
compatible with the diagonals. -/
theorem exists_isOpen_subset_compl_range_diagonal_of_isOpenImmersion (f : P ⟶ S)
    {V : Scheme.{u}} (j : V ⟶ P) [IsSeparated (j ≫ f)]
    (m : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f) [IsOpenImmersion m]
    (hm : Set.range m = pullback.fst f f ⁻¹' Set.range j ∩ pullback.snd f f ⁻¹' Set.range j)
    (hΔ : pullback.diagonal (j ≫ f) ≫ m = j ≫ pullback.diagonal f) {z : ↥(pullback f f)}
    (hz : z ∉ Set.range (pullback.diagonal f)) (h₁ : pullback.fst f f z ∈ Set.range j)
    (h₂ : pullback.snd f f z ∈ Set.range j) :
    ∃ t ⊆ (Set.range (pullback.diagonal f))ᶜ, IsOpen t ∧ z ∈ t := by
  obtain ⟨w, rfl⟩ : z ∈ Set.range m := by
    rw [hm]
    exact ⟨h₁, h₂⟩
  have hw : w ∉ Set.range (pullback.diagonal (j ≫ f)) := by
    rintro ⟨y, rfl⟩
    exact hz ⟨j y, by rw [← Scheme.Hom.comp_apply, ← hΔ, Scheme.Hom.comp_apply]⟩
  refine ⟨m '' (Set.range (pullback.diagonal (j ≫ f)))ᶜ, ?_,
    m.isOpenEmbedding.isOpenMap _
      (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range.isOpen_compl,
    ⟨w, hw, rfl⟩⟩
  rintro _ ⟨n, hn, rfl⟩ ⟨x, hx⟩
  have hxj : x ∈ Set.range j := by
    have hn' : m n ∈ Set.range m := ⟨n, rfl⟩
    rw [hm] at hn'
    have h := hn'.1
    rw [Set.mem_preimage, ← hx, pullback_fst_diagonal_apply] at h
    exact h
  obtain ⟨y, rfl⟩ := hxj
  exact hn ⟨y, m.isOpenEmbedding.injective
    (by rw [← Scheme.Hom.comp_apply, hΔ, Scheme.Hom.comp_apply, hx])⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The nested case.** For an open immersion `j : V ⟶ P` with `V ⟶ S` separated, a point
`z ∈ P ×_S P` off the diagonal whose two projections lie in `V` has an open neighbourhood missing
the diagonal: the image of the complement of the diagonal of `V` under the open immersion
`V ×_S V ⟶ P ×_S P`. -/
theorem exists_isOpen_subset_compl_range_diagonal (f : P ⟶ S) {V : Scheme.{u}} (j : V ⟶ P)
    [IsOpenImmersion j] [IsSeparated (j ≫ f)] {z : ↥(pullback f f)}
    (hz : z ∉ Set.range (pullback.diagonal f)) (h₁ : pullback.fst f f z ∈ Set.range j)
    (h₂ : pullback.snd f f z ∈ Set.range j) :
    ∃ t ⊆ (Set.range (pullback.diagonal f))ᶜ, IsOpen t ∧ z ∈ t :=
  exists_isOpen_subset_compl_range_diagonal_of_isOpenImmersion f j
    (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp))
    (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _) (by apply pullback.hom_ext <;> simp) hz h₁ h₂

/-- **Separatedness from a cover by separated opens, any two disjoint or nested in a third**: if
the opens `U i` cover `P`, each `U i ⟶ S` is separated, and any two of them are disjoint or both
contained in some `U k`, then `f : P ⟶ S` is separated. This contains the two cases of Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 28 (disjoint unions and increasing unions of
separated open subschemes). -/
theorem isSeparated_of_cover_of_disjoint_or_le (f : P ⟶ S) {ι : Type*} (U : ι → P.Opens)
    (hU : ⨆ i, U i = ⊤) (hsep : ∀ i, IsSeparated ((U i).ι ≫ f))
    (hpair : ∀ i j, Disjoint (U i) (U j) ∨ ∃ k, U i ≤ U k ∧ U j ≤ U k) :
    IsSeparated f := by
  have hcov (x : P) : ∃ i, x ∈ U i := by
    rw [← TopologicalSpace.Opens.mem_iSup, hU]
    trivial
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨i, hi⟩ := hcov (pullback.fst f f z)
  obtain ⟨j, hj⟩ := hcov (pullback.snd f f z)
  rcases hpair i j with hdisj | ⟨k, hik, hjk⟩
  · refine ⟨pullback.fst f f ⁻¹' (U i : Set P) ∩ pullback.snd f f ⁻¹' (U j : Set P), ?_,
      ((U i).isOpen.preimage (pullback.fst f f).continuous).inter
        ((U j).isOpen.preimage (pullback.snd f f).continuous), hi, hj⟩
    rintro _ ⟨hwi, hwj⟩ ⟨x, rfl⟩
    rw [Set.mem_preimage, pullback_fst_diagonal_apply] at hwi
    rw [Set.mem_preimage, pullback_snd_diagonal_apply] at hwj
    have hx : x ∈ U i ⊓ U j := ⟨hwi, hwj⟩
    simpa using hdisj.le_bot hx
  · have := hsep k
    refine exists_isOpen_subset_compl_range_diagonal f (U k).ι hz ?_ ?_
    · rw [Scheme.Opens.range_ι]
      exact hik hi
    · rw [Scheme.Opens.range_ι]
      exact hjk hj

/-- A cover of `P` by pairwise disjoint opens, each separated over `S`, makes `P ⟶ S`
separated (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, disjoint unions). -/
theorem isSeparated_of_cover_of_pairwise_disjoint (f : P ⟶ S) {ι : Type*} (U : ι → P.Opens)
    (hU : ⨆ i, U i = ⊤) (hsep : ∀ i, IsSeparated ((U i).ι ≫ f))
    (hdisj : Pairwise (Function.onFun Disjoint U)) : IsSeparated f := by
  classical
  refine isSeparated_of_cover_of_disjoint_or_le f U hU hsep fun i j => ?_
  by_cases hij : i = j
  · exact Or.inr ⟨i, le_rfl, hij ▸ le_rfl⟩
  · exact Or.inl (hdisj hij)

/-- A directed cover of `P` by opens, each separated over `S`, for example an increasing union,
makes `P ⟶ S` separated (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, increasing
unions). -/
theorem isSeparated_of_cover_of_directed (f : P ⟶ S) {ι : Type*} (U : ι → P.Opens)
    (hU : ⨆ i, U i = ⊤) (hsep : ∀ i, IsSeparated ((U i).ι ≫ f))
    (hdir : Directed (· ≤ ·) U) : IsSeparated f :=
  isSeparated_of_cover_of_disjoint_or_le f U hU hsep fun i j => Or.inr (hdir i j)

/-- **Strata form**: opens `U i m` covering `P`, each separated over `S`, monotone in `m` for a
directed order and disjoint for distinct `i`, make `P ⟶ S` separated. This is the form of a cover
of a Picard scheme by strata, disjoint for distinct polynomials `φ` and increasing in the
level (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–29). -/
theorem isSeparated_of_cover_of_disjoint_of_monotone (f : P ⟶ S) {ι κ : Type*} [Preorder κ]
    [IsDirected κ (· ≤ ·)] (U : ι → κ → P.Opens) (hU : ⨆ i, ⨆ m, U i m = ⊤)
    (hsep : ∀ i m, IsSeparated ((U i m).ι ≫ f)) (hmono : ∀ i, Monotone (U i))
    (hdisj : ∀ i i' m m', i ≠ i' → Disjoint (U i m) (U i' m')) : IsSeparated f := by
  refine isSeparated_of_cover_of_disjoint_or_le f (fun x : ι × κ => U x.1 x.2)
    (by rw [iSup_prod]; exact hU) (fun x => hsep x.1 x.2) fun x y => ?_
  by_cases hxy : x.1 = y.1
  · obtain ⟨m, hxm, hym⟩ := directed_of (· ≤ ·) x.2 y.2
    refine Or.inr ⟨(x.1, m), hmono x.1 hxm, ?_⟩
    rw [hxy]
    exact hmono y.1 hym
  · exact Or.inl (hdisj x.1 y.1 x.2 y.2 hxy)

end AlgebraicGeometry
