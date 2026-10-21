/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.GradedCohomologyBounds
public import Aglib.RingTheory.AdicCompletion.TowerComparison

/-!
# Canonical completion comparison from finite actual Rees cohomology

The map exists without finiteness hypotheses and is induced by the original
coefficient reductions. Its bijectivity here is explicitly conditional on finite
actual Rees cohomology in two adjacent degrees, for the single compatible action.
The geometric Rees comparison discharges those conditions in the proper theorem.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) (I : Ideal A) (p : ℕ)

/-- The original reductions, viewed as the linear family used by native completion. -/
abbrev idealPowerCohomologyReductionMap (n : ℕ) :
    (moduleCohomologyFunctorOfHom X α p).obj F →ₗ[A]
      (idealPowerQuotientCohomology X α F I p).obj (op n) :=
  ((idealPowerQuotientCohomologyReduction X α F I p).app (op n)).hom

/-- The original linear reduction family is compatible with the actual inverse tower. -/
theorem idealPowerCohomologyReductionMap_compatible {m n : ℕ} (h : m ≤ n) :
    (AdicCompletion.towerTransition (idealPowerQuotientCohomology X α F I p) h).comp
        (idealPowerCohomologyReductionMap X α F I p n) =
      idealPowerCohomologyReductionMap X α F I p m := by
  let η := idealPowerQuotientCohomologyReduction X α F I p
  exact congrArg (fun f => f.hom)
    ((η.naturality (homOfLE h).op).symm.trans (Category.id_comp _))

/-- The canonical completion-to-cohomology-tower map, defined without finiteness assumptions. -/
def idealPowerCohomologyCompletionMap :
    AdicCompletion I ((moduleCohomologyFunctorOfHom X α p).obj F) →ₗ[A]
      ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I p) :=
  AdicCompletion.completionToSections I (idealPowerQuotientCohomology X α F I p)
    (idealPowerCohomologyReductionMap X α F I p)
    (idealPowerCohomologyReductionMap_compatible X α F I p)
    (fun n => idealPowerQuotientReduction_pow_le_ker X α F I n p)

/-- Completion of an original class evaluates to its original coefficient reduction. -/
theorem idealPowerCohomologyCompletionMap_of
    (x : (moduleCohomologyFunctorOfHom X α p).obj F) (n : ℕ) :
    (idealPowerCohomologyCompletionMap X α F I p (AdicCompletion.of I _ x)).val (op n) =
      moduleCohomologyMapOfHom X α (idealQuotientπ X α F (I ^ n)) p x := rfl

variable [IsNoetherianRing A]
variable [Module (reesAlgebra I) (idealPowerCohomologyTotal X α F I p)]
variable [Module (reesAlgebra I) (idealPowerCohomologyTotal X α F I (p + 1))]
variable [Module.Finite (reesAlgebra I) (idealPowerCohomologyTotal X α F I p)]
variable [Module.Finite (reesAlgebra I) (idealPowerCohomologyTotal X α F I (p + 1))]
variable (hp : IdealPowerCohomologyActionCompatible X α F I p)
variable (hp1 : IdealPowerCohomologyActionCompatible X α F I (p + 1))

include hp hp1 in
/-- Finite actual Rees cohomology in adjacent degrees makes the canonical map bijective. -/
theorem idealPowerCohomologyCompletionMap_bijective_of_finite_reesCohomology :
    Function.Bijective (idealPowerCohomologyCompletionMap X α F I p) := by
  obtain ⟨a, ha⟩ := idealPowerCohomology_exists_image_bound X α F I p hp
  obtain ⟨b, hb⟩ := idealPowerCohomology_exists_kernel_bound X α F I (p + 1) hp1
  apply AdicCompletion.completionToSections_bijective I
    (idealPowerQuotientCohomology X α F I p)
    (idealPowerCohomologyReductionMap X α F I p)
    (idealPowerCohomologyReductionMap_compatible X α F I p)
    (fun n => idealPowerQuotientReduction_pow_le_ker X α F I n p) a b
  · intro n
    exact idealPowerQuotientReduction_ker_le_of_image_le X α F I n (n + a) p (ha n)
  · intro n y hy
    obtain ⟨x, rfl⟩ := hy
    exact idealPowerQuotientMap_mem_range_of_kernel_killed X α F I
      (Nat.le_add_right n b) p (hb n) x

/-- The canonical equivalence, conditional on finite actual compatible Rees cohomology. -/
def idealPowerCohomologyCompletionEquivOfFiniteReesCohomology :
    AdicCompletion I ((moduleCohomologyFunctorOfHom X α p).obj F) ≃ₗ[A]
      ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I p) :=
  LinearEquiv.ofBijective (idealPowerCohomologyCompletionMap X α F I p)
    (idealPowerCohomologyCompletionMap_bijective_of_finite_reesCohomology X α F I p hp hp1)

end AlgebraicGeometry.Scheme.Cohomology
