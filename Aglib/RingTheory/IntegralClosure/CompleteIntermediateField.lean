/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.CompleteLocalSurface
public import Aglib.RingTheory.CompleteDVRExtension
public import Aglib.RingTheory.AdicCompletion.FiniteLocalComplete
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# The actual complete intermediate integral closure

For a finite normal domain over an original complete local domain of dimension
at most two, the integral closure in an actual intermediate fraction field is
finite, local, complete and normal. Its map into the original upper ring is the
native integral-closure lift, and its original fraction-field equation is kept.

The fields are the native fraction rings. Their action is the existing
`FractionRing.liftAlgebra` of the original faithful coefficient map. No regularity
of the lower ring or completeness of the upper ring is required for this assembly.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace integralClosure

universe u

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]

attribute [local instance] FractionRing.liftAlgebra

/-- The original finite coefficient algebra induces a finite extension of its
native fraction fields, with the native lifted action. -/
theorem completeIntermediate_fieldFinite :
    FiniteDimensional (FractionRing R) (FractionRing A) :=
  IsFractionRing.finite_of_finite_algebra R A (FractionRing R) (FractionRing A)

attribute [local instance] completeIntermediate_fieldFinite

variable (L : IntermediateField (FractionRing R) (FractionRing A))

local notation "B" => integralClosure R L

/-- The literal intermediate closure has the original intermediate field as its
fraction field. -/
theorem completeIntermediate_fractionRing : IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension (FractionRing R) L

/-- Normality concerns the literal integral closure, not a replacement ring. -/
theorem completeIntermediate_normal : IsIntegrallyClosed B :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)

/-- The original coefficient map into this literal closure is injective. -/
theorem completeIntermediate_base_injective : Function.Injective (algebraMap R B) := by
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R (FractionRing R) L
  let : Module.IsTorsionFree R B := IsIntegralClosure.isTorsionFree R L
  exact FaithfulSMul.algebraMap_injective R B

/-- The original integral coefficient map reflects units. -/
theorem completeIntermediate_base_isLocalHom : IsLocalHom (algebraMap R B) := by
  let : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R L
  exact (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
    (completeIntermediate_base_injective R A L)

attribute [local instance] completeIntermediate_base_isLocalHom

/-- The unchanged inclusion through the original intermediate field into the
original upper fraction field. -/
def intermediateAmbientMap : B →ₐ[R] FractionRing A :=
  (L.val.restrictScalars R).comp (integralClosure R L).val

omit [Module.Finite R A] in
@[simp]
theorem intermediateAmbientMap_apply (b : B) :
    intermediateAmbientMap R A L b = ((b : L) : FractionRing A) := rfl

/-- The original ambient action is pinned before installing the B-action on A. -/
@[instance_reducible]
def intermediateAmbientAlgebra : Algebra B (FractionRing A) :=
  (intermediateAmbientMap R A L).toRingHom.toAlgebra

attribute [local instance 1100] intermediateAmbientAlgebra

omit [Module.Finite R A] in
theorem intermediateAmbient_scalarTower :
    @IsScalarTower R B (FractionRing A)
      (inferInstance : Algebra R B).toSMul
      (intermediateAmbientAlgebra R A L).toSMul
      (inferInstance : Algebra R (FractionRing A)).toSMul := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((intermediateAmbientMap R A L).commutes r).symm

attribute [local instance] intermediateAmbient_scalarTower

omit [Module.Finite R A] in
theorem intermediateAmbientMap_injective : Function.Injective (intermediateAmbientMap R A L) := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  exact h

section OriginalRing

variable [IsIntegrallyClosed A]

/-- The canonical map from the actual intermediate closure to the original
normal ring is the native integral-closure lift through its original fractions. -/
def intermediateToOriginal : B →ₐ[R] A := by
  let : IsIntegralClosure A R (FractionRing A) := inferInstance
  let : Algebra B (FractionRing A) := intermediateAmbientAlgebra R A L
  let := intermediateAmbient_scalarTower R A L
  let : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R L
  exact IsIntegralClosure.lift R A (FractionRing A) (S := B)

/-- The lift retains the original inclusion into the unchanged upper fractions. -/
theorem intermediateToOriginal_fraction (b : B) :
    algebraMap A (FractionRing A) (intermediateToOriginal R A L b) =
      intermediateAmbientMap R A L b := by
  let : IsIntegralClosure A R (FractionRing A) := inferInstance
  let : Algebra B (FractionRing A) := intermediateAmbientAlgebra R A L
  let := intermediateAmbient_scalarTower R A L
  let : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R L
  exact IsIntegralClosure.algebraMap_lift R A (FractionRing A) (S := B) b

/-- The actual lift is injective, as witnessed by its original fraction equation. -/
theorem intermediateToOriginal_injective : Function.Injective (intermediateToOriginal R A L) := by
  intro b c h
  apply intermediateAmbientMap_injective R A L
  exact (intermediateToOriginal_fraction R A L b).symm.trans
    ((congrArg (algebraMap A (FractionRing A)) h).trans
      (intermediateToOriginal_fraction R A L c))

/-- The B-action on A is induced by this actual integral-closure lift. -/
@[instance_reducible]
def intermediateOriginalAlgebra : Algebra B A :=
  (intermediateToOriginal R A L).toRingHom.toAlgebra

attribute [local instance] intermediateOriginalAlgebra

/-- The original R-action is preserved by the canonical intermediate lift. -/
theorem intermediateToOriginal_scalarTower : IsScalarTower R B A := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((intermediateToOriginal R A L).commutes r).symm

attribute [local instance] intermediateToOriginal_scalarTower

/-- The upper original fraction map has the same B-action as the intermediate
field inclusion; this is proved, not chosen as a separate compatibility input. -/
theorem intermediateToOriginal_fractionTower :
    @IsScalarTower B A (FractionRing A)
      (intermediateOriginalAlgebra R A L).toSMul
      (inferInstance : Algebra A (FractionRing A)).toSMul
      (intermediateAmbientAlgebra R A L).toSMul := by
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (intermediateToOriginal_fraction R A L b).symm

/-- The original upper algebra is finite over the actual intermediate closure. -/
theorem intermediateToOriginal_finite : Module.Finite B A :=
  Module.Finite.of_restrictScalars_finite R B A

/-- The original intermediate lift reflects units by finite injective integrality. -/
theorem intermediateToOriginal_isLocalHom :
    IsLocalHom (intermediateToOriginal R A L).toRingHom := by
  let : Algebra B A := intermediateOriginalAlgebra R A L
  let : Module.Finite B A := intermediateToOriginal_finite R A L
  have hInt : (algebraMap B A).IsIntegral :=
    (algebraMap_isIntegral_iff (R := B) (A := A)).mpr (Algebra.IsIntegral.of_finite B A)
  exact hInt.isLocalHom (intermediateToOriginal_injective R A L)

/-- The actual closure has dimension two by the two original integral
contractions. No general dimension-equality or selected-stalk premise is used. -/
theorem completeIntermediate_dimension (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2) :
    ringKrullDim B = 2 := by
  let : Algebra B A := intermediateOriginalAlgebra R A L
  let : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R L
  let : Module.Finite B A := intermediateToOriginal_finite R A L
  let : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hBA : ringKrullDim A ≤ ringKrullDim B := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B A))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under (R := B) (I := p.asIdeal) (J := q.asIdeal) hpq
  have hRB : ringKrullDim B ≤ ringKrullDim R := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R B))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under (R := R) hpq
  exact le_antisymm (hRB.trans hR.le) (hA.symm.le.trans hBA)

end OriginalRing

section CompleteBase

variable [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] [Ring.KrullDimLE 2 R]

/-- CN2 applies to the literal intermediate closure in its actual finite field. -/
theorem completeIntermediate_finite : Module.Finite R B :=
  integralClosure.finite_of_complete_local_dimLE_two R (FractionRing R) L

attribute [local instance] completeIntermediate_finite

/-- Noetherianity follows from the proved finite original coefficient algebra. -/
theorem completeIntermediate_noetherian : IsNoetherianRing B := by
  let : Module.Finite R B := completeIntermediate_finite R A L
  exact IsNoetherianRing.of_finite R B

attribute [local instance] completeIntermediate_noetherian

/-- The actual finite domain over the complete original local ring is local. -/
theorem completeIntermediate_local : IsLocalRing B := by
  let : Module.Finite R B := completeIntermediate_finite R A L
  exact IsDiscreteValuationRing.CompleteExtension.isLocalRing_of_finite R B

attribute [local instance] completeIntermediate_local

/-- The actual maximal-adic completeness follows from finite-module completeness
and the proved cofinal comparison of its two original ideals. -/
theorem completeIntermediate_complete : IsAdicComplete (maximalIdeal B) B := by
  let : Module.Finite R B := completeIntermediate_finite R A L
  let : IsLocalRing B := completeIntermediate_local R A L
  let : IsLocalHom (algebraMap R B) := completeIntermediate_base_isLocalHom R A L
  exact IsAdicComplete.maximalIdeal_of_finite_local R B

end CompleteBase

end integralClosure
