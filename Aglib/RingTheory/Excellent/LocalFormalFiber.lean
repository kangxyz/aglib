/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.Defs
public import Aglib.RingTheory.AdicCompletion.RingEquiv
public import Aglib.RingTheory.AdicCompletion.RegularGenericFormalFiber
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Finite generic formal fibres of local G-rings

Only the maximal-prime component of the G-ring property is used. The local
localization, its completion, and the tensor scalar change are actual native
objects and equivalences. In particular no polynomial stability of G-rings is
assumed here.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace AdicCompletion

/-- A local algebra equivalence induces an algebra equivalence of the actual
maximal-ideal completions. -/
def localCompletionAlgEquiv
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [IsLocalRing R] [IsLocalRing B] [Algebra R B]
    (e : B ≃ₐ[R] R) :
    AdicCompletion (maximalIdeal B) B ≃ₐ[R]
      AdicCompletion (maximalIdeal R) R := by
  let c : AdicCompletion (maximalIdeal B) B ≃ₐ[R]
      AdicCompletion ((maximalIdeal B).map e.toRingEquiv.toRingHom) R :=
    { AdicCompletion.congrRingEquiv e.toRingEquiv (maximalIdeal B) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R B
          (AdicCompletion (maximalIdeal B) B)]
        change AdicCompletion.congrRingEquiv e.toRingEquiv (maximalIdeal B)
          (algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap R B r)) = _
        rw [AdicCompletion.congrRingEquiv_algebraMap]
        exact congrArg
          (algebraMap R
            (AdicCompletion ((maximalIdeal B).map e.toRingEquiv.toRingHom) R))
          (e.commutes r) }
  have hI : (maximalIdeal B).map e.toRingEquiv.toRingHom = maximalIdeal R :=
    map_ringEquiv_maximalIdeal e.toRingEquiv
  exact hI ▸ c

end AdicCompletion

namespace IsGRing

/-- The finite generic formal-fibre test for a local G-ring domain, retaining the
original compatible action of `R` on the finite field extension. -/
theorem regular_finiteGenericFormalFibre
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsGRing R)
    (E : Type u) [Field E] [Algebra R E] [Algebra (FractionRing R) E]
    [IsScalarTower R (FractionRing R) E] [FiniteDimensional (FractionRing R) E] :
    IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] E) := by
  let B := Localization.AtPrime (maximalIdeal R)
  let C := AdicCompletion (maximalIdeal B) B
  let e : B ≃ₐ[R] R :=
    (IsLocalization.atUnits R (maximalIdeal R).primeCompl
      (fun x => by simpa using! fun a => a)).symm
  let : Algebra B (FractionRing R) :=
    ((algebraMap R (FractionRing R)).comp e.toRingEquiv.toRingHom).toAlgebra
  let : IsFractionRing B (FractionRing R) :=
    IsFractionRing.of_ringEquiv_left e.toRingEquiv (fun _ => rfl)
  let : Algebra B E :=
    ((algebraMap R E).comp e.toRingEquiv.toRingHom).toAlgebra
  let : IsScalarTower B (FractionRing R) E := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    change algebraMap R E (e b) =
      algebraMap (FractionRing R) E (algebraMap R (FractionRing R) (e b))
    exact IsScalarTower.algebraMap_apply R (FractionRing R) E (e b)
  let : IsScalarTower R B E := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap R E r = algebraMap R E (e (algebraMap R B r))
    simp only [e.commutes, Algebra.algebraMap_self_apply]
  have hsurj : Function.Surjective (algebraMap R B) := by
    intro b
    refine ⟨e b, ?_⟩
    apply e.injective
    simp only [e.commutes, Algebra.algebraMap_self_apply]
  let : TensorProduct.CompatibleSMul R B C E :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective C E hsurj
  have hreg : IsRegularRing (C ⊗[B] E) :=
    Algebra.IsRegularMap.regular_finiteGenericFibre B C
      (h.2 (maximalIdeal R)) (FractionRing R) E
  let := hreg
  let changeBase : C ⊗[B] E ≃ₐ[R] C ⊗[R] E :=
    Algebra.TensorProduct.equivOfCompatibleSMul R B R C E
  let changeCompletion : C ⊗[R] E ≃ₐ[R]
      AdicCompletion (maximalIdeal R) R ⊗[R] E :=
    Algebra.TensorProduct.congr (AdicCompletion.localCompletionAlgEquiv e)
      (AlgEquiv.refl : E ≃ₐ[R] E)
  exact IsRegularRing.of_ringEquiv (R := C ⊗[B] E)
    (changeBase.trans changeCompletion).toRingEquiv

/-- For a G-ring DVR, the regular generic formal fibres imply the intrinsic
geometric-reducedness condition on the completed fraction field. -/
theorem hasGeometricallyReducedFractionCompletion
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : IsGRing R) : AdicCompletion.HasGeometricallyReducedFractionCompletion R := by
  apply
    AdicCompletion.hasGeometricallyReducedFractionCompletion_of_regularFiniteGenericFormalFibres R
  intro E _ _ _ _ _
  exact regular_finiteGenericFormalFibre R h E

end IsGRing
