/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineOpen
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # A genuine finite etale cover after shrinking an integral affine base

The existing generic-finiteness theorem makes the original affine etale map
finite on a nonempty open. The original image is dense because the source is
nonempty and the map is open. Its pullback is still dense, and finiteness makes
that image closed, proving actual surjectivity. A further affine refinement
retains all of these properties. No Noetherian hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

/-- A nonempty affine etale chart of an integral affine scheme becomes an
actual finite etale surjective cover on a nonempty dense affine open. -/
theorem exists_dense_finiteEtale_open_of_isAffineHom
    {Y X : Scheme.{u}} [IsAffine X] [IsIntegral X] [Nonempty Y]
    (f : Y ⟶ X) [IsAffineHom f] [Etale f] :
    ∃ (S : Scheme.{u}) (j : S ⟶ X), IsAffine S ∧ IsOpenImmersion j ∧
      Nonempty S ∧ IsDominant j ∧ IsFinite (pullback.snd f j) ∧
      Etale (pullback.snd f j) ∧ Surjective (pullback.snd f j) := by
  obtain ⟨U, a, ha, hU, hfinite⟩ := exists_nonempty_finite_open_of_isAffineHom f
  have : IsOpenImmersion a := ha
  have : Nonempty U := hU
  have : IsFinite (pullback.snd f a) := hfinite
  have hd : DenseRange f := f.isOpenMap.denseRange_of_isPreirreducibleSpace
  let x : U := Classical.choice hU
  obtain ⟨A, b, hb, ⟨z, _⟩, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) (by simp)
  have : IsOpenImmersion b := hb
  have : Nonempty (Spec A) := ⟨z⟩
  let j := b ≫ a
  have : IsFinite (pullback.snd f j) :=
    (isFinite_pullback_snd_comp_iff f a b).mpr inferInstance
  have : IsDominant (pullback.snd f j) := ⟨by
    change Dense (Set.range (pullback.snd f j))
    rw [Scheme.Pullback.range_snd]
    exact hd.preimage j.isOpenMap⟩
  exact ⟨Spec A, j, inferInstance, inferInstance, inferInstance,
    ⟨j.isOpenMap.denseRange_of_isPreirreducibleSpace⟩, inferInstance, inferInstance,
    surjective_of_isDominant_of_isClosed_range _
      (pullback.snd f j).isClosedMap.isClosed_range⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
