/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentPoint
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.LocalDecomposition
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-! # Literal scheme triangles for common-field finite component points -/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable (R A Ω : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [CommRing A] [Algebra R A] [Module.Finite R A]
  [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω] (m : MaximalSpectrum A)

local instance : Module.Finite R (Localization.AtPrime m.asIdeal) :=
  HenselianLocalRing.finite_localizationAtPrime R A m.asIdeal

local instance : IsLocalHom (algebraMap R (Localization.AtPrime m.asIdeal)) := by
  apply ((local_hom_TFAE (algebraMap R (Localization.AtPrime m.asIdeal))).out 5 1).mp
  exact eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
      (maximalIdeal (Localization.AtPrime m.asIdeal)))

/-- The geometric point is exactly the extension of the original local-component
residue point, not a chosen replacement point with merely equal support. -/
theorem finiteComponentPoint_spec_eq :
    Spec.map (CommRingCat.ofHom (finiteComponentPoint R A Ω m)) =
      Spec.map (CommRingCat.ofHom
        (finiteLocalResidueEmbedding R (Localization.AtPrime m.asIdeal) Ω).toRingHom) ≫
      LocalRing.residueSpecMap (Localization.AtPrime m.asIdeal) ≫
      Finite.localComponentInclusion A m := by
  change Spec.map (CommRingCat.ofHom (finiteComponentPoint R A Ω m)) =
    Spec.map (CommRingCat.ofHom
      (finiteLocalResidueEmbedding R (Localization.AtPrime m.asIdeal) Ω).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Localization.AtPrime m.asIdeal))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m.asIdeal)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The extended original component point lies over the fixed common-field base
point, as an equality of the original scheme morphisms. -/
theorem finiteComponentPoint_spec_comp :
    Spec.map (CommRingCat.ofHom (finiteComponentPoint R A Ω m)) ≫
      Spec.algebraMap R A =
    Spec.map (CommRingCat.ofHom
      ((algebraMap (ResidueField R) Ω).comp (IsLocalRing.residue R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun a => Spec.map (CommRingCat.ofHom a))
    (finiteComponentPoint_comp_algebraMap R A Ω m)

end AlgebraicGeometry.Scheme.EtaleCohomology
