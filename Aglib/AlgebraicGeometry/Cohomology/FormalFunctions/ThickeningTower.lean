/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningCohomology
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTower
public import Aglib.Algebra.Category.ModuleCat.FunctorTransport

/-!
# The actual infinitesimal-thickening cohomology tower

Every stage is original cohomology on the actual base change by `Spec (A/I^n)`.
Every transition is the actual geometric cohomology map along the corresponding
closed immersion. The diagram isomorphism with quotient cohomology is induced
by the original coefficient comparisons and is retained on compatible families.
The index includes zero.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent]
  (I : Ideal A) (p : ℕ)

local notation "α" => idealThickeningBaseScalar f

/-- The original cohomology of actual ideal-power thickenings, with original
geometric transition maps, indexed by all natural numbers including zero. -/
def idealThickeningCohomologyTower : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  ModuleCat.functorOfLinearEquiv (idealPowerQuotientCohomology X α F I p)
    (fun n => idealThickeningCohomology f F (I ^ n.unop) p)
    (fun φ => idealThickeningCohomologyMap f F (Ideal.pow_le_pow_right (leOfHom φ.unop)) p)
    (fun n => idealQuotientThickeningCohomologyEquiv f F (I ^ n.unop) p)
    (fun φ => idealQuotientThickeningCohomologyEquiv_naturality f F
      (Ideal.pow_le_pow_right (leOfHom φ.unop)) p)

/-- The original quotient and geometric thickening diagrams are naturally
isomorphic, through the original stagewise cohomology comparisons. -/
def idealQuotientThickeningCohomologyTowerIso :
    idealPowerQuotientCohomology X α F I p ≅ idealThickeningCohomologyTower f F I p :=
  ModuleCat.functorOfLinearEquivIso (idealPowerQuotientCohomology X α F I p)
    (fun n => idealThickeningCohomology f F (I ^ n.unop) p)
    (fun φ => idealThickeningCohomologyMap f F (Ideal.pow_le_pow_right (leOfHom φ.unop)) p)
    (fun n => idealQuotientThickeningCohomologyEquiv f F (I ^ n.unop) p)
    (fun φ => idealQuotientThickeningCohomologyEquiv_naturality f F
      (Ideal.pow_le_pow_right (leOfHom φ.unop)) p)

/-- The natural diagram comparison acts coordinatewise on actual compatible
families, without a choice of abstract inverse-limit objects. -/
def idealQuotientThickeningSectionsEquiv :
    ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I p) ≃ₗ[A]
      ModuleCat.sectionsSubmodule (idealThickeningCohomologyTower f F I p) :=
  ModuleCat.sectionsSubmoduleCongr (idealQuotientThickeningCohomologyTowerIso f F I p)

/-- The compatible-family equivalence uses exactly the original stage maps. -/
@[simp]
theorem idealQuotientThickeningSectionsEquiv_apply
    (s : ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I p)) (n : ℕ) :
    (idealQuotientThickeningSectionsEquiv f F I p s).val (op n) =
      idealQuotientThickeningCohomologyEquiv f F (I ^ n) p (s.val (op n)) := rfl

end AlgebraicGeometry.Scheme.Cohomology
