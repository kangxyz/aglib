/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationMap
public import Aglib.RingTheory.Henselian.HenselizationFiniteLocalEquiv

/-!
# Finite henselization after an actual local-ring equivalence

The henselized-base action on an equivalent local ring's henselization is the
explicit composite of the actual finite-local base lift and the constructed
henselization equivalence. This action is finite, and its original-base square
is verified directly.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Henselization.FiniteLocalFactor

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
  (q : Ideal B) [q.IsMaximal]
  {S : Type w} [CommRing S] [IsLocalRing S]
  (e : Localization.AtPrime q ≃+* S)

/-- The actual transported henselized-base ring map. -/
def transportedBaseMap : Henselization R →+* Henselization S :=
  (Henselization.equivOfRingEquiv e).toRingHom.comp (baseLift R B q).toRingHom

/-- The scalar action is defined by the displayed ring map. -/
abbrev transportedBaseAlgebra : Algebra (Henselization R) (Henselization S) :=
  (transportedBaseMap R B q e).toAlgebra

/-- The genuine henselization equivalence is linear over the transported base. -/
def transportedEquiv :
    letI := transportedBaseAlgebra R B q e
    Henselization (Localization.AtPrime q) ≃ₐ[Henselization R] Henselization S := by
  letI := transportedBaseAlgebra R B q e
  exact { Henselization.equivOfRingEquiv e with commutes' := fun _ => rfl }

/-- The transported action is finite, by the proved finite-local henselization theorem. -/
theorem finite_transport :
    letI := transportedBaseAlgebra R B q e
    Module.Finite (Henselization R) (Henselization S) := by
  let := transportedBaseAlgebra R B q e
  let := finite_henselization R B q
  exact Module.Finite.of_surjective (transportedEquiv R B q e).toLinearMap
    (transportedEquiv R B q e).surjective

/-- The transported map has the correct square with the original base. -/
@[simp] theorem transportedBaseMap_algebraMap (r : R) :
    transportedBaseMap R B q e (algebraMap R (Henselization R) r) =
      algebraMap S (Henselization S) (e (algebraMap R (Localization.AtPrime q) r)) := by
  change Henselization.equivOfRingEquiv e
    (baseLift R B q (algebraMap R (Henselization R) r)) = _
  rw [(baseLift R B q).commutes]
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime q)
    (Henselization (Localization.AtPrime q))]
  exact Henselization.equivOfRingEquiv_algebraMap e _

end Henselization.FiniteLocalFactor
