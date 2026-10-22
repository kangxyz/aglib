/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FractionBaseChange
public import Aglib.RingTheory.AdicCompletion.GeometricallyReducedFraction

/-!
# Finite generic formal fibres and the intrinsic completion condition

The input is reducedness of the actual finite generic formal fibres, not an
approximation supplier. Only finite extensions in the base universe are tested.
The output retains the literal canonical `FractionRing.liftAlgebra` action.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace AdicCompletion

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The tensor comparison's fraction action is the canonical lifted action.
Equality of actions follows from their common restriction to the original ring. -/
theorem fractionCompletionAlgebra_eq_liftAlgebra :
    letI := faithfulSMul_maximalIdeal R
    fractionCompletionAlgebra R (FractionRing R) =
      FractionRing.liftAlgebra R
        (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
  let := faithfulSMul_maximalIdeal R
  let := FractionRing.liftAlgebra R
    (FractionRing (AdicCompletion (maximalIdeal R) R))
  let := FractionRing.isScalarTower_liftAlgebra R
    (FractionRing (AdicCompletion (maximalIdeal R) R))
  have h : fractionRingMap R (FractionRing R) =
      algebraMap (FractionRing R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    rw [fractionRingMap_algebraMap,
      ← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)),
      ← IsScalarTower.algebraMap_apply R (FractionRing R)
        (FractionRing (AdicCompletion (maximalIdeal R) R))]
  apply Algebra.algebra_ext
  intro x
  exact RingHom.congr_fun h x

/-- Reducedness of every finite extension of the actual generic formal fibre
supplies geometric reducedness of the completed fraction field.

The `R`-action on the finite extension is constrained by the displayed scalar
tower, so it is precisely restriction of the original fraction-field action.
No regularity or Noetherianity of an infinite-field base change is assumed. -/
theorem hasGeometricallyReducedFractionCompletion_of_finiteGenericFormalFibres
    (h : ∀ (E : Type u) [Field E] [Algebra R E] [Algebra (FractionRing R) E]
      [IsScalarTower R (FractionRing R) E] [FiniteDimensional (FractionRing R) E],
      IsReduced (AdicCompletion (maximalIdeal R) R ⊗[R] E)) :
    HasGeometricallyReducedFractionCompletion R := by
  have hgeom :
      letI := fractionCompletionAlgebra R (FractionRing R)
      Algebra.IsGeometricallyReduced (FractionRing R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
    let := fractionCompletionAlgebra R (FractionRing R)
    apply Algebra.IsGeometricallyReduced.of_finiteExtensions
    intro E _ _ _
    let : Algebra R E :=
      ((algebraMap (FractionRing R) E).comp (algebraMap R (FractionRing R))).toAlgebra
    let : IsScalarTower R (FractionRing R) E :=
      IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    let : IsReduced (AdicCompletion (maximalIdeal R) R ⊗[R] E) := h E
    let e := fractionCompletionBaseChangeAlgEquiv R (FractionRing R) E
    let : IsReduced
        (FractionRing (AdicCompletion (maximalIdeal R) R) ⊗[FractionRing R] E) :=
      isReduced_of_injective e e.injective
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm (FractionRing R) E
        (FractionRing (AdicCompletion (maximalIdeal R) R)))
      (Algebra.TensorProduct.comm (FractionRing R) E
        (FractionRing (AdicCompletion (maximalIdeal R) R))).injective
  let := faithfulSMul_maximalIdeal R
  exact (congrArg
    (fun a : Algebra (FractionRing R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) ↦
      @Algebra.IsGeometricallyReduced (FractionRing R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) _ _ a)
    (fractionCompletionAlgebra_eq_liftAlgebra R)).mp hgeom

end AdicCompletion
