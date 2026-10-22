/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.ModificationCover
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenRestriction

/-! # Actual initial proper models for the finite boundary construction -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- Concrete initial data, constructed below from the actual compactifiable
modification theorem. The common open is not asserted to be schematically
dense in each individual proper model. -/
structure InitialPatchFamily {X S : Scheme.{u}} (p : X ⟶ S) where
  n : ℕ
  W : Fin (n + 1) → X.Opens
  U : X.Opens
  dense : Dense (U : Set X)
  le : ∀ a, U ≤ W a
  cover : ∀ x : X, ∃ a, x ∈ W a
  C : Fin (n + 1) → Over S
  proper : ∀ a, IsProper (C a).hom
  V : ∀ a, (C a).left.Opens
  denseV : ∀ a, Dense (V a : Set (C a).left)
  dominantV : ∀ a, IsSchemeTheoreticallyDominant (V a).ι
  q : ∀ a, (V a).toScheme ⟶ X
  properQ : ∀ a, IsProper (q a)
  isoQ : ∀ a, IsIso (q a ∣_ W a)
  over : ∀ a, (V a).ι ≫ (C a).hom = q a ≫ p
  s : ∀ a, (W a).toScheme ⟶ (V a).toScheme
  openS : ∀ a, IsOpenImmersion (s a)
  dominantS : ∀ a, IsSchemeTheoreticallyDominant (s a)
  source : ∀ a, s a ≫ q a = (W a).ι

/-- The initial proper-model family is constructed from finite-type geometry,
not assumed as a compactification provider. The nonempty-source hypothesis
is used only to select a chart for the nonempty finite index. -/
theorem exists_initialPatchFamily
    {X S : Scheme.{u}} [IsNoetherian S] [Nonempty X]
    (p : X ⟶ S) [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] :
    Nonempty (InitialPatchFamily p) := by
  classical
  obtain ⟨ι, hι, W, hW, hcover, hinter⟩ :=
    exists_finite_dense_compactifiable_modification_cover p
  let : Fintype ι := hι
  have H := fun a => (hW a).2.2
  choose T Y b pY e t hT hY hseq hb hiso hpY he ht htd hted hed hbase htb using H
  let : ∀ a, IsOpenImmersion (e a) := he
  let : ∀ a, IsOpenImmersion (t a) := ht
  let : ∀ a, IsSchemeTheoreticallyDominant (t a) := htd
  let : ∀ a, IsSchemeTheoreticallyDominant (t a ≫ e a) := hted
  let : ∀ a, IsSchemeTheoreticallyDominant (e a) := fun a =>
    IsSchemeTheoreticallyDominant.of_comp_right (t a) (e a)
  let : ∀ a, IsProper (b a) := hb
  let : ∀ a, IsIso (b a ∣_ W a) := hiso
  have hιne : Nonempty ι := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hx : x ∈ (⨆ a, W a) := by rw [hcover]; trivial
    obtain ⟨a, _⟩ := Opens.mem_iSup.mp hx
    exact ⟨a⟩
  let a₀ : ι := Classical.choice hιne
  let ind : Fin (Fintype.card ι + 1) → ι :=
    Fin.cases a₀ (Fintype.equivFin ι).symm
  have hind : Function.Surjective ind := by
    intro a
    refine ⟨((Fintype.equivFin ι) a).succ, ?_⟩
    exact (Fintype.equivFin ι).symm_apply_apply a
  let C : Fin (Fintype.card ι + 1) → Over S := fun a => Over.mk (pY (ind a))
  let V : ∀ a, (C a).left.Opens := fun a => (e (ind a)).opensRange
  let q : ∀ a, (V a).toScheme ⟶ X := fun a =>
    (e (ind a)).isoOpensRange.inv ≫ b (ind a)
  let s : ∀ a, (W (ind a)).toScheme ⟶ (V a).toScheme := fun a =>
    t (ind a) ≫ (e (ind a)).isoOpensRange.hom
  refine ⟨{
    n := Fintype.card ι
    W := fun a => W (ind a)
    U := ⨅ a, W a
    dense := hinter
    le := fun a => iInf_le W (ind a)
    cover := ?_
    C := C
    proper := fun a => hpY (ind a)
    V := V
    denseV := ?_
    dominantV := ?_
    q := q
    properQ := ?_
    isoQ := ?_
    over := ?_
    s := s
    openS := ?_
    dominantS := ?_
    source := ?_ }⟩
  · intro x
    have hx : x ∈ (⨆ a, W a) := by rw [hcover]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    obtain ⟨j, rfl⟩ := hind a
    exact ⟨j, ha⟩
  · intro a
    exact hed (ind a)
  · intro a
    dsimp only [V]
    rw [← Hom.isoOpensRange_inv_comp]
    infer_instance
  · intro a
    dsimp only [q]
    infer_instance
  · intro a
    dsimp only [q]
    exact Scheme.Hom.isIso_restrict_comp (e (ind a)).isoOpensRange.inv
      (b (ind a)) (W (ind a))
  · intro a
    change (e (ind a)).opensRange.ι ≫ pY (ind a) =
      ((e (ind a)).isoOpensRange.inv ≫ b (ind a)) ≫ p
    rw [← (e (ind a)).isoOpensRange_inv_comp, Category.assoc,
      hbase (ind a), Category.assoc]
  · intro a
    dsimp only [s]
    infer_instance
  · intro a
    dsimp only [s]
    infer_instance
  · intro a
    dsimp only [s, q]
    rw [Category.assoc, Iso.hom_inv_id_assoc, htb]

end AlgebraicGeometry.Scheme.Compactification
