/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientChartTower
public import Aglib.RingTheory.AdicCompletion.HomComparison

/-!
# Original formal morphisms on an affine chart

Conjugating the actual quotient-tower morphism by the canonical chart quotient
comparisons gives compatible quotient linear maps over the chart ring.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F G : X.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent] (I : Ideal A)

local notation "α" => idealThickeningBaseScalar f

/-- A natural transformation of the original quotient diagrams induces the
actual compatible quotient maps on every affine chart. -/
def localQuotientHom
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U : X.affineOpens) :
    AdicCompletion.CompatibleQuotientHom (I.map (idealSectionRingHom X α U.val))
      Γ(F, U) Γ(G, U) := by
  refine ⟨fun n => (idealPowerQuotientAffineChartEquiv f G I U n).symm.toLinearMap ∘ₗ
    ((η.app (op n)).val.app (op U.val)).hom ∘ₗ
      (idealPowerQuotientAffineChartEquiv f F I U n).toLinearMap, ?_⟩
  intro m n h
  apply LinearMap.ext
  intro x
  apply (idealPowerQuotientAffineChartEquiv f G I U m).injective
  change idealPowerQuotientAffineChartEquiv f G I U m
      (Submodule.factorPow _ Γ(G, U) h
        ((idealPowerQuotientAffineChartEquiv f G I U n).symm
          ((η.app (op n)).val.app (op U.val)
            (idealPowerQuotientAffineChartEquiv f F I U n x)))) =
    idealPowerQuotientAffineChartEquiv f G I U m
      ((idealPowerQuotientAffineChartEquiv f G I U m).symm
        ((η.app (op m)).val.app (op U.val)
          (idealPowerQuotientAffineChartEquiv f F I U m
            (Submodule.factorPow _ Γ(F, U) h x))))
  rw [idealPowerQuotientAffineChartEquiv_transition,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    idealPowerQuotientAffineChartEquiv_transition]
  exact (congrArg (fun k => k.val.app (op U.val)
    (idealPowerQuotientAffineChartEquiv f F I U n x))
      (η.naturality (homOfLE h).op)).symm

/-- On an original section the affine formal map retains the original
coefficient reduction followed by the original tower morphism. -/
theorem localQuotientHom_mk
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U : X.affineOpens) (n : ℕ) (x : Γ(F, U)) :
    (localQuotientHom f F G I η U).val n (Submodule.Quotient.mk x) =
      (idealPowerQuotientAffineChartEquiv f G I U n).symm
        ((η.app (op n)).val.app (op U.val)
          ((idealQuotientπ X α F (I ^ n)).app U.val x)) := by
  change (idealPowerQuotientAffineChartEquiv f G I U n).symm
      ((η.app (op n)).val.app (op U.val)
        (idealPowerQuotientAffineChartEquiv f F I U n (Submodule.Quotient.mk x))) = _
  rw [idealPowerQuotientAffineChartEquiv_mk]

/-- Affine restriction of an original source section commutes with the actual
formal morphism, expressed in the original quotient sheaf rather than an
auxiliary semilinear quotient transport. -/
theorem localQuotientHom_mk_restrict
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U V : X.affineOpens) (i : V.val ⟶ U.val) (n : ℕ) (x : Γ(F, U)) :
    idealPowerQuotientAffineChartEquiv f G I V n
        ((localQuotientHom f F G I η V).val n
          (Submodule.Quotient.mk (F.val.map i.op x))) =
      (idealQuotient X α G (I ^ n)).val.map i.op
        (idealPowerQuotientAffineChartEquiv f G I U n
          ((localQuotientHom f F G I η U).val n (Submodule.Quotient.mk x))) := by
  simp only [localQuotientHom_mk, LinearEquiv.apply_symm_apply]
  exact (congrArg ((η.app (op n)).val.app (op V.val))
    (_root_.PresheafOfModules.naturality_apply
      (idealQuotientπ X α F (I ^ n)).val i.op x)).trans
        (_root_.PresheafOfModules.naturality_apply (η.app (op n)).val i.op
          ((idealQuotientπ X α F (I ^ n)).app U.val x))

end AlgebraicGeometry.Scheme.Cohomology
