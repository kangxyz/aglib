/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisAffineChart
public import Aglib.AlgebraicGeometry.Morphisms.Etale.LocalSectionNeighborhood

/-! # The original Galois normalization near a local section

One original etale point over the closed section point suffices: original
Galois fibre transitivity removes the whole finite branch fibre, and the
canonical target open retains the entire local section by specialization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The canonical branch-complement open of the original normalization retains
its original local section. No etaleness away from this open is asserted. -/
theorem range_subset_etaleTargetOpen_of_section_etaleAt
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (j : U ⟶ X) [IsOpenImmersion j]
    (Y : Scheme.FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y]
    (s : Spec (.of R) ⟶ X)
    (a : Spec (.of R) ⟶ (genericMap j Y.obj.hom).normalization)
    (ha : a ≫ (genericMap j Y.obj.hom).fromNormalization = s)
    (het : (genericMap j Y.obj.hom).fromNormalization.etaleAt
      (a (IsLocalRing.closedPoint R))) :
    letI : IsFinite (genericMap j Y.obj.hom).fromNormalization :=
      fromNormalization_isFinite j Y.obj.hom
    Set.range s ⊆ (genericMap j Y.obj.hom).fromNormalization.etaleTargetOpen
      (genericMap j Y.obj.hom).fromNormalization.isClosedMap := by
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  apply Hom.range_subset_etaleTargetOpen_of_local_closedFiber f s
  intro y hy
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s (IsLocalRing.closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hs : f (a (IsLocalRing.closedPoint R)) = s (IsLocalRing.closedPoint R) :=
    congrArg (fun g : Spec (.of R) ⟶ X => g (IsLocalRing.closedPoint R)) ha
  exact genericNormalization_etaleAt_of_image_eq_in_affineOpen j Y V hV
    (a (IsLocalRing.closedPoint R)) y (hs.symm ▸ hx) (hs.trans hy.symm) het

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
