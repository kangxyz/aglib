/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteDedekindBranches

/-!
# The actual completed-base action on every local completion branch

The completed-base action is induced by the constructed tensor product identification,
not supplied as an extra branch-compatibility premise.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

universe u
variable {R S : Type u} [CommRing R] [IsNoetherianRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [DecidableEq (Ideal S)]

/-- The action of the completed base on an actual local completion branch. -/
@[instance_reducible] def localCompletionBaseAlgebra (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (q : IdealBranch (I.map (algebraMap R S))) :
    Algebra (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) :=
  (((Pi.evalRingHom _ q).comp (tensorEquivLocalCompletions I hI).toRingHom).comp
    Algebra.TensorProduct.includeLeftRingHom).toAlgebra

/-- The proved full branch product respects the actual completed-base action. -/
def tensorEquivLocalCompletionsBase (I : Ideal R) (hI : I.map (algebraMap R S) ≠ 0) :
    letI := fun q ↦ localCompletionBaseAlgebra I hI q
    AdicCompletion I R ⊗[R] S ≃ₐ[AdicCompletion I R]
      ∀ q : IdealBranch (I.map (algebraMap R S)),
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val) := by
  letI := fun q ↦ localCompletionBaseAlgebra I hI q
  exact AlgEquiv.ofRingEquiv (f := (tensorEquivLocalCompletions I hI).toRingEquiv)
    (fun _ ↦ rfl)

/-- The completed-base action agrees with the original base-ring action. -/
theorem localCompletionBaseIsScalarTower (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (q : IdealBranch (I.map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra I hI q
    IsScalarTower R (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) := by
  let := localCompletionBaseAlgebra I hI q
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrFun ((tensorEquivLocalCompletions I hI).commutes r) q).symm

/-- Every actual completed branch remains finite over the completed base. -/
theorem localCompletionBaseFinite (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (q : IdealBranch (I.map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra I hI q
    Module.Finite (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) := by
  let := fun q ↦ localCompletionBaseAlgebra I hI q
  have := Module.Finite.of_surjective
    (tensorEquivLocalCompletionsBase I hI).toLinearMap
    (tensorEquivLocalCompletionsBase I hI).surjective
  exact Module.Finite.of_pi (R := AdicCompletion I R)
    (fun q : IdealBranch (I.map (algebraMap R S)) ↦
      AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) q

end AdicCompletion
