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

namespace ModuleCat

universe u v w w'

/-- Construct the specified diagram and its original comparison together over
variable original families, retaining the prescribed transition maps. -/
def functorWithLinearEquivIso
    {R : Type u} [Ring R] {J : Type w} [Category.{w'} J]
    (P : J ⥤ ModuleCat.{v} R) (Q : J → ModuleCat.{v} R)
    (T : ∀ {a b : J}, (a ⟶ b) → (Q a ⟶ Q b))
    (e : ∀ a, P.obj a ≃ₗ[R] Q a)
    (h : ∀ {a b : J} (φ : a ⟶ b) (x : P.obj a), T φ (e a x) = e b (P.map φ x)) :
    Σ Q' : J ⥤ ModuleCat.{v} R, P ≅ Q' :=
  ⟨functorOfLinearEquiv P Q T e h, functorOfLinearEquivIso P Q T e h⟩

end ModuleCat

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent]
  (I : Ideal A) (p : ℕ)

local notation "α" => idealThickeningBaseScalar f

/-- The whole original object family, including the zeroth thickening. -/
def thickeningObjects : ℕᵒᵖ → ModuleCat.{u + 1} A :=
  fun n => idealThickeningCohomology f F (I ^ n.unop) p

/-- The whole original geometric transition family on those same objects. -/
def thickeningTransitions :
    ∀ {a b : ℕᵒᵖ}, (a ⟶ b) →
      (thickeningObjects f F I p a ⟶ thickeningObjects f F I p b) :=
  fun φ => idealThickeningCohomologyMap f F (Ideal.pow_le_pow_right (leOfHom φ.unop)) p

/-- The whole original comparison family on the prescribed objects. -/
def thickeningEquivalences :
    ∀ n : ℕᵒᵖ, (idealPowerQuotientCohomology X α F I p).obj n ≃ₗ[A]
      thickeningObjects f F I p n :=
  fun n => idealQuotientThickeningCohomologyEquiv f F (I ^ n.unop) p

/-- The original full family law, with unchanged actual transition maps. -/
theorem thickeningNaturality :
    ∀ {a b : ℕᵒᵖ} (φ : a ⟶ b) (x : (idealPowerQuotientCohomology X α F I p).obj a),
      thickeningTransitions f F I p φ (thickeningEquivalences f F I p a x) =
        thickeningEquivalences f F I p b
          ((idealPowerQuotientCohomology X α F I p).map φ x) :=
  fun φ => idealQuotientThickeningCohomologyEquiv_naturality f F
    (Ideal.pow_le_pow_right (leOfHom φ.unop)) p

/-- One actual construction of the diagram and its original comparison. -/
def thickeningDiagramWithComparison :
    Σ Q : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A, idealPowerQuotientCohomology X α F I p ≅ Q :=
  ModuleCat.functorWithLinearEquivIso (idealPowerQuotientCohomology X α F I p)
    (thickeningObjects f F I p) (thickeningTransitions f F I p)
    (thickeningEquivalences f F I p) (thickeningNaturality f F I p)

/-- The original cohomology of actual ideal-power thickenings, with original
geometric transition maps, indexed by all natural numbers including zero. -/
def idealThickeningCohomologyTower : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  (thickeningDiagramWithComparison f F I p).1

/-- The original quotient and geometric thickening diagrams are naturally
isomorphic, through the same construction's original stagewise comparisons. -/
def idealQuotientThickeningCohomologyTowerIso :
    idealPowerQuotientCohomology X α F I p ≅ idealThickeningCohomologyTower f F I p :=
  (thickeningDiagramWithComparison f F I p).2

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
