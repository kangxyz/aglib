/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Limits

/-! # The actual faithfully flat algebra of a finite affine étale family

The disjoint-union map is used only to obtain the algebra for Amitsur descent.
It is not asserted to belong to the original covering sieve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The original global-section ring map of a jointly surjective finite affine
étale family is faithfully flat. No flatness is imposed on a coefficient module. -/
theorem finiteAffineFamily_faithfullyFlat
    {W : Scheme.{u}} [IsAffine W] {ι : Type v} [Finite ι]
    (U : ι → Scheme.{u}) [∀ i, IsAffine (U i)] (f : ∀ i, U i ⟶ W)
    [∀ i, Etale (f i)] (hcover : ∀ x : W, ∃ i y, f i y = x) :
    (Sigma.desc f).appTop.hom.FaithfullyFlat := by
  have : Flat (Sigma.desc f) := inferInstance
  have : Surjective (Sigma.desc f) := ⟨by
    intro x
    obtain ⟨i, y, rfl⟩ := hcover x
    exact ⟨Sigma.ι U i y, by simp [← Scheme.Hom.comp_apply]⟩⟩
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (Sigma.desc f)).mp
    ⟨inferInstance, inferInstance⟩

/-- Actual covering-sieve membership supplies the joint-surjectivity input. -/
theorem etaleFamily_jointlySurjective {X : Scheme.{u}} {W : X.Etale}
    {ι : Type*} (U : ι → Over W)
    (hcover : Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈
      smallEtaleTopology X W) :
    ∀ x : W.left, ∃ i y, (U i).hom.left y = x := by
  have h := (ofArrows_mem_smallEtaleTopology_iff (fun i => (U i).hom)).mp hcover
  intro x
  have hx : x ∈ ⋃ i, Set.range (U i).hom.left := by rw [h]; trivial
  simpa only [Set.mem_iUnion, Set.mem_range] using hx

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
