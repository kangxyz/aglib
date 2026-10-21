/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.TensorCentre
public import Aglib.RingTheory.Localization.IdealSpreading
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # A genuine finite-type principal open carrying the extended centre

Finite generation is derived from the original finite-type algebra and the
constructed source DVR. It is not postulated for either actual centre ideal.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace SeparableResidueExtension

variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]

/-- The base DVR acts on the coefficient field through the specified residue extension. -/
local instance tensorFiniteOpenResidueAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (f : B →ₐ[R] E)

/-- The actual tensor is finite type over the constructed right-hand source DVR. -/
instance tensor_finiteType : Algebra.FiniteType (Ring R E) (B ⊗[R] Ring R E) :=
  Algebra.FiniteType.of_surjective
    (Algebra.TensorProduct.commRight R (Ring R E) B).toAlgHom
    (Algebra.TensorProduct.commRight R (Ring R E) B).surjective

/-- The actual tensor is Noetherian without any domain assumption. -/
instance tensor_isNoetherianRing : IsNoetherianRing (B ⊗[R] Ring R E) :=
  Algebra.FiniteType.isNoetherianRing (Ring R E) (B ⊗[R] Ring R E)

/-- Every actual principal open is still finite type over the source DVR. -/
theorem tensor_away_finiteType (s : B ⊗[R] Ring R E) :
    Algebra.FiniteType (Ring R E) (Localization.Away s) := inferInstance

/-- The actual extended original centre agrees with the actual rational centre
on one principal open. Finite generation is derived, not supplied. -/
theorem exists_tensor_centre_open (hf : Function.Surjective f) :
    ∃ s : B ⊗[R] Ring R E,
      s ∉ SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f) ∧
      ((RingHom.ker f.toRingHom).map
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Ring R E)).map
          (algebraMap (B ⊗[R] Ring R E) (Localization.Away s)) =
      (SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f)).map
          (algebraMap (B ⊗[R] Ring R E) (Localization.Away s)) := by
  let I : Ideal (B ⊗[R] Ring R E) :=
    (RingHom.ker f.toRingHom).map
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Ring R E)
  let J := SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f)
  have hloc : I.map (algebraMap _ (Localization.AtPrime J)) =
      J.map (algebraMap _ (Localization.AtPrime J)) := by
    change I.map (algebraMap _ (CentreRing R E f)) =
      J.map (algebraMap _ (CentreRing R E f))
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal J (CentreRing R E f)]
    change ((RingHom.ker f.toRingHom).map
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Ring R E)).map _ = _
    rw [← ker_tensorResidue R E f hf]
    exact SeparableTensorDiagonal.map_ker_eq_maximalIdeal (ResidueField R) E
      (tensorResidue R E f) (tensorResidue_surjective R E f hf)
  exact Ideal.exists_away_map_eq_of_atPrime_map_eq J I J
    I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing hloc

end SeparableResidueExtension
