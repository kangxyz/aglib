/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.LocalGeometricPoint
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GeometricPointKernel

/-! # The common geometric point attached to an actual finite local component -/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
  (Ω : Type w) [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω]
  (m : MaximalSpectrum A)

local instance : Module.Finite R (Localization.AtPrime m.asIdeal) :=
  HenselianLocalRing.finite_localizationAtPrime R A m.asIdeal

local instance : IsLocalHom (algebraMap R (Localization.AtPrime m.asIdeal)) := by
  apply ((local_hom_TFAE (algebraMap R (Localization.AtPrime m.asIdeal))).out 5 1).mp
  exact eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
      (maximalIdeal (Localization.AtPrime m.asIdeal)))

/-- The point of the finite algebra obtained from the original maximal localization
and its unique residue embedding into the chosen algebraically closed field. -/
def finiteComponentPoint : A →+* Ω :=
  (finiteLocalGeometricPoint R (Localization.AtPrime m.asIdeal) Ω).comp
    (algebraMap A (Localization.AtPrime m.asIdeal))

/-- This is an actual point over the fixed base geometric point. -/
theorem finiteComponentPoint_comp_algebraMap :
    (finiteComponentPoint R A Ω m).comp (algebraMap R A) =
      (algebraMap (ResidueField R) Ω).comp (residue R) := by
  change ((finiteLocalGeometricPoint R (Localization.AtPrime m.asIdeal) Ω).comp
    (algebraMap A (Localization.AtPrime m.asIdeal))).comp (algebraMap R A) = _
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  exact finiteLocalGeometricPoint_comp_algebraMap R (Localization.AtPrime m.asIdeal) Ω

/-- The constructed common-field point selects exactly the prescribed component. -/
theorem finiteComponentPoint_ker :
    RingHom.ker (finiteComponentPoint R A Ω m) = m.asIdeal := by
  change RingHom.ker (((finiteLocalResidueEmbedding R
    (Localization.AtPrime m.asIdeal) Ω).toRingHom.comp
      (residue (Localization.AtPrime m.asIdeal))).comp
        (algebraMap A (Localization.AtPrime m.asIdeal))) = _
  rw [RingHom.comp_assoc,
    RingHom.ker_comp_of_injective _
      (finiteLocalResidueEmbedding R (Localization.AtPrime m.asIdeal) Ω).injective,
    ← RingHom.comap_ker, ker_residue]
  exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime m.asIdeal) m.asIdeal

/-- Distinct finite local components give distinct actual common-field points. -/
theorem finiteComponentPoint_injective : Function.Injective (finiteComponentPoint R A Ω) := by
  intro m n h
  apply MaximalSpectrum.ext
  have hk := congrArg RingHom.ker h
  simpa only [finiteComponentPoint_ker] using hk

end AlgebraicGeometry.Scheme.EtaleCohomology
