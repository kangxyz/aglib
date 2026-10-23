/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Finite affine refinements in the original small étale topology

Every covering sieve on an affine étale object contains a finite jointly
surjective family of affine objects. The members individually belong to the
original sieve. Their disjoint-union map need not belong to that sieve, so this
statement deliberately does not claim cofinality of singleton affine covers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- A covering sieve over an affine object admits a genuine finite affine refinement. -/
theorem exists_finite_affine_family {X : Scheme.{u}} (W : X.Etale) [IsAffine W.left]
    (R : Sieve W) (hR : R ∈ Scheme.smallEtaleTopology X W) :
    ∃ (n : ℕ) (V : Fin n → X.Etale) (f : ∀ i, V i ⟶ W),
      (∀ i, IsAffine (V i).left) ∧ (∀ i, R (f i)) ∧
      Sieve.ofArrows V f ∈ Scheme.smallEtaleTopology X W := by
  classical
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology W R).mp hR
  let : 𝒰.Over X := hOver
  let (i : 𝒰.I₀) : (𝒰.X i).Over X := hOver.over i
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  have (i : 𝒰.I₀) : Etale (𝒰.X i ↘ X) := hEtale i
  let : AlgebraicGeometry.QuasiCompactCover 𝒰.toPreZeroHypercover :=
    AlgebraicGeometry.QuasiCompactCover.of_isOpenMap (fun i => (𝒰.f i).isOpenMap)
  obtain ⟨n, a, U, hU, hcover⟩ :=
    AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact
      𝒰.toPreZeroHypercover (U := ⊤) (isAffineOpen_top W.left).isCompact
  let V : Fin n → X.Etale := fun i => Etale.mk ((U i).ι ≫ (𝒰.X (a i) ↘ X))
  let g : ∀ i, V i ⟶ (𝒰.X (a i)).asOverProp X (hEtale (a i)) :=
    fun i => MorphismProperty.Over.homMk (U i).ι rfl
  let f : ∀ i, V i ⟶ W := fun i => g i ≫ (𝒰.f (a i)).asOverProp X
  refine ⟨n, V, f, fun i => hU i, ?_, ?_⟩
  · intro i
    exact R.downward_closed (hle _ _ ⟨a i⟩) (g i)
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    have hx : x ∈ ⋃ i, 𝒰.f (a i) '' (U i) := by rw [hcover]; trivial
    obtain ⟨i, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, ⟨y, hy⟩, hxy⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
