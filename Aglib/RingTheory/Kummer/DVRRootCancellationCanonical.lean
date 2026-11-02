/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.DVRRootCancellation

/-! # Original DVR root cancellation with constructed strict fraction maps

Only the original fraction fields are inputs. The fraction fields of the
actual pointed etale colimit and its literal root algebra are chosen internally;
all their maps and the compatibility square are constructed by fraction lifting.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)] [IsSepClosed Ω]
  (N : ℕ) (π : R)
  (K F L : Type u)
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field F] [Algebra R F] [Algebra (RootAlgebra N π) F]
  [IsScalarTower R (RootAlgebra N π) F] [IsFractionRing (RootAlgebra N π) F]
  [Algebra K F] [IsScalarTower R K F]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

include Ω

/-- Bounded cancellation for the unchanged original normalized generic tensor.
The strict fraction fields, their maps, and the fraction square are not inputs. -/
theorem dvrRoot_normalTensor_etale_of_geometricPoint
    (hN : 0 < N) (hπ : Irreducible π) (hunit : IsUnit (N : R))
    (hcard : Nat.card (L ≃ₐ[K] L) ∣ N) :
    Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] L)) := by
  let C := GeometricEtaleColimit R Ω
  let T := RootAlgebra N π
  let T' := RootAlgebra N (algebraMap R C π)
  let : IsDomain C := GeometricEtaleColimit.isDomain_of_dvr R Ω
  let : IsDiscreteValuationRing C := GeometricEtaleColimit.isDiscreteValuationRing_of_dvr R Ω
  let : IsDomain T := uniformizerRoot_isDomain R π hπ N hN
  let : IsDomain T' := strictHenselianRoot_isDomain R Ω N π hN hπ
  let : Algebra T T' := rootBaseChangeAlgebra C N π
  let : Module.FaithfullyFlat T T' := strictHenselianRoot_faithfullyFlat R Ω N π
  let : Module.Free C T' := uniformizerRoot_free C (algebraMap R C π) N hN
  let K' := FractionRing C
  let F' := FractionRing T'
  let : IsScalarTower R C K' := inferInstance
  let : IsScalarTower R T' F' := inferInstance
  let : IsScalarTower C T' F' := inferInstance
  let : IsScalarTower T T' F' := inferInstance
  let : IsScalarTower R T T' := IsScalarTower.of_algHom (rootBaseChangeHom C N π)
  let : IsScalarTower R T F' := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap T' F' (algebraMap R T' r) =
      algebraMap T' F' (algebraMap T T' (algebraMap R T r))
    rw [← IsScalarTower.algebraMap_apply R T T']
  let : IsScalarTower R C F' := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap T' F' (algebraMap R T' r) =
      algebraMap T' F' (algebraMap C T' (algebraMap R C r))
    rw [← IsScalarTower.algebraMap_apply R C T']
  have hRK : Function.Injective (algebraMap R K') := by
    exact (IsFractionRing.injective C K').comp
      (GeometricEtaleColimit.algebraMap_injective_of_dvr R Ω)
  have hTF : Function.Injective (algebraMap T F') :=
    (IsFractionRing.injective T' F').comp (FaithfulSMul.algebraMap_injective T T')
  have hCF : Function.Injective (algebraMap C F') :=
    (IsFractionRing.injective T' F').comp (FaithfulSMul.algebraMap_injective C T')
  let fK : K →ₐ[R] K' := IsFractionRing.liftAlgHom (g := Algebra.ofId R K') hRK
  let : Algebra K K' := fK.toRingHom.toAlgebra
  let : IsScalarTower R K K' := IsScalarTower.of_algHom fK
  let fF : F →ₐ[T] F' := IsFractionRing.liftAlgHom (g := Algebra.ofId T F') hTF
  let : Algebra F F' := fF.toRingHom.toAlgebra
  let : IsScalarTower T F F' := IsScalarTower.of_algHom fF
  let fK' : K' →ₐ[C] F' := IsFractionRing.liftAlgHom (g := Algebra.ofId C F') hCF
  let : Algebra K' F' := fK'.toRingHom.toAlgebra
  let : IsScalarTower C K' F' := IsScalarTower.of_algHom fK'
  let : Algebra K F' := ((algebraMap F F').comp (algebraMap K F)).toAlgebra
  let : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq' rfl
  have hsquare : (algebraMap K' F').comp (algebraMap K K') = algebraMap K F' := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    change fK' (fK (algebraMap R K r)) = fF (algebraMap K F (algebraMap R K r))
    rw [fK.commutes, ← IsScalarTower.algebraMap_apply R K F,
      IsScalarTower.algebraMap_apply R T F, fF.commutes,
      IsScalarTower.algebraMap_apply R C K', fK'.commutes]
    exact (IsScalarTower.algebraMap_apply R C F' r).symm.trans
      (IsScalarTower.algebraMap_apply R T F' r)
  let : IsScalarTower K K' F' := IsScalarTower.of_algebraMap_eq' hsquare.symm
  exact dvrRoot_normalTensor_etale R Ω N π K F L K' F' hN hπ hunit hcard

end Algebra.Kummer
