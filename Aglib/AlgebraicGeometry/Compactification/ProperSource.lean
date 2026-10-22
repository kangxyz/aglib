/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion

/-!
# Properness from a proper source containing a dense image

An actual map from a proper scheme to a separated finite-type target is proper.
If its image contains a prescribed dense image, it is surjective, and properness
descends by the native universally closed surjective-source theorem.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- A proper source whose image contains an actual dense map proves properness
of the target. All maps and both structural triangles are retained explicitly. -/
theorem proper_of_dense_map_lift {P Z S U : Scheme.{u}}
    (pP : P ⟶ S) [IsProper pP] (pZ : Z ⟶ S)
    [IsSeparated pZ] [LocallyOfFiniteType pZ]
    (G : P ⟶ Z) (hG : G ≫ pZ = pP)
    (g : U ⟶ Z) (hg : DenseRange g) (t : U ⟶ P) (ht : t ≫ G = g) :
    IsProper G ∧ Surjective G ∧ IsProper pZ := by
  let : IsProper (G ≫ pZ) := hG.symm ▸ inferInstance
  let : IsProper G := IsProper.of_comp G pZ
  have hsub : Set.range g ⊆ Set.range G := by
    rw [← ht]
    exact Set.range_comp_subset_range t G
  have hd : Dense (Set.range G) := Dense.mono hsub hg
  have hr : Set.range G = Set.univ := by
    rw [← G.isClosedMap.isClosed_range.closure_eq]
    exact hd.closure_eq
  let : Surjective G := ⟨Set.range_eq_univ.mp hr⟩
  exact ⟨inferInstance, inferInstance,
    OpenNormalizationGluing.proper_of_surjective_proper_source G pZ⟩

end AlgebraicGeometry.Scheme.Compactification
