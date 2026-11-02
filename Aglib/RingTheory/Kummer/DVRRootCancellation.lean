/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.StrictHenselianRootNormalization
public import Aglib.RingTheory.Kummer.StrictHenselianRootBaseChange
public import Aglib.RingTheory.Kummer.StrictHenselianTensorCancellation
public import Aglib.RingTheory.IntegralClosure.FiniteEtale.GenericBaseChange
public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue
public import Mathlib.RingTheory.Etale.Descent

/-! # Bounded root cancellation over the original DVR

The strict extension is the actual pointed etale colimit. Its original
normalization comparison, fraction pushout, and selected generic-field
cancellation identify the same base-changed normalization. Faithfully flat
etale descent returns to the original root algebra.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)] [IsSepClosed Ω]
  (N : ℕ) (π : R)

local notation "C" => GeometricEtaleColimit R Ω
local notation "T" => RootAlgebra N π
local notation "T'" => RootAlgebra N (algebraMap R C π)

/-- The base-change algebra structure from the root algebra `T` to `T'`. -/
local instance : Algebra T T' := rootBaseChangeAlgebra C N π

variable (K F L K' F' : Type u)
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field F] [Algebra R F] [Algebra (RootAlgebra N π) F]
  [IsScalarTower R (RootAlgebra N π) F]
  [IsFractionRing (RootAlgebra N π) F] [Algebra K F] [IsScalarTower R K F]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field K'] [Algebra (GeometricEtaleColimit R Ω) K']
  [IsFractionRing (GeometricEtaleColimit R Ω) K'] [Algebra K K']
  [Field F'] [Algebra (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) π)) F']
  [IsFractionRing (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) π)) F']
  [Algebra (RootAlgebra N π) F']
  [IsScalarTower (RootAlgebra N π)
    (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) π)) F']
  [Algebra (GeometricEtaleColimit R Ω) F']
  [IsScalarTower (GeometricEtaleColimit R Ω)
    (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) π)) F']
  [Algebra K' F'] [IsScalarTower (GeometricEtaleColimit R Ω) K' F']
  [Algebra F F'] [IsScalarTower (RootAlgebra N π) F F']
  [Algebra K F'] [IsScalarTower K F F'] [IsScalarTower K K' F']

include Ω K' F'

omit [IsFractionRing R K] in
/-- The original normalized generic tensor is etale after the bounded root
extension. No strict-basechange normalization or etaleness hypothesis is retained. -/
theorem dvrRoot_normalTensor_etale (hN : 0 < N) (hπ : Irreducible π)
    (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N) :
    Algebra.Etale T (integralClosure T (F ⊗[K] L)) := by
  let := GeometricEtaleColimit.isDomain_of_dvr R Ω
  let := GeometricEtaleColimit.isDiscreteValuationRing_of_dvr R Ω
  let := uniformizerRoot_isDomain R π hπ N hN
  let := uniformizerRoot_isDiscreteValuationRing R π hπ N hN
  have hπ' := GeometricEtaleColimit.irreducible_algebraMap_of_dvr R Ω hπ
  let := uniformizerRoot_isDomain C (algebraMap R C π) hπ' N hN
  let := uniformizerRoot_isDiscreteValuationRing C (algebraMap R C π) hπ' N hN
  let : Module.FaithfullyFlat T T' := strictHenselianRoot_faithfullyFlat R Ω N π
  let : FaithfulSMul C F' := (faithfulSMul_iff_algebraMap_injective C F').mpr (by
    rw [IsScalarTower.algebraMap_eq C K' F']
    exact (algebraMap K' F').injective.comp (IsFractionRing.injective C K'))
  have hunit' : IsUnit (N : C) := by
    simpa only [map_natCast] using hunit.map (algebraMap R C)
  let : Algebra.Etale T' (integralClosure T' (F' ⊗[K'] (K' ⊗[K] L))) :=
    strictHenselian_normalBaseChangeTensor_etale C K L K' (algebraMap R C π)
      hπ' N hN hunit' hcard F'
  let eA := IsDiscreteValuationRing.genericTensorBaseChange T T' F F' K K' L
    (FaithfulSMul.algebraMap_injective T T')
  let e := (strictRootIntegralClosureEquiv R Ω N π (F ⊗[K] L) hN).trans
    eA.mapIntegralClosure
  let : Algebra.Etale T' (T' ⊗[T] integralClosure T (F ⊗[K] L)) :=
    Algebra.Etale.of_equiv
      (A := integralClosure T' (F' ⊗[K'] (K' ⊗[K] L))) e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T'


end Algebra.Kummer
