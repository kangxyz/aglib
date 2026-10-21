/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TowerGeneration
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientChart

/-! # Generation of a formal coherent system from its special fibre -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

local instance formalGenerationCoefficient_isQuasicoherent (n : ℕ) :
    (F.obj.obj (op n)).IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (F.property.coherent n R j).1)

/-- The original finite-stage transition kernel on an affine open lies in
the original ideal multiple. This is a consequence of the canonical adic
reduction isomorphism, not an additional formal-system premise. -/
theorem formalTransition_affine_kernel_le {n m : ℕ} (h : n ≤ m) (U : X.affineOpens) :
    LinearMap.ker ((F.obj.map (homOfLE h).op).val.app (op U.val)).hom ≤
      ((idealThickeningIdealSheaf f I).ideal U) ^ n •
        (⊤ : Submodule Γ(X, U.val) Γ(F.obj.obj (op m), U.val)) := by
  let q := idealQuotientAffineChartEquiv f (F.obj.obj (op m)) (I ^ n) U
  let e := ((idealSectionsFunctor X U.val).mapIso (baseIdealReductionIso f I F h)).toLinearEquiv
  intro x hx
  have hx' : (F.obj.map (homOfLE h).op).app U.val x = 0 := hx
  have hc : e (q (Submodule.Quotient.mk x)) =
      (F.obj.map (homOfLE h).op).app U.val x := by
    change (baseIdealReductionIso f I F h).hom.app U.val
      ((idealQuotientπ X (idealThickeningBaseScalar f)
        (F.obj.obj (op m)) (I ^ n)).app U.val x) = _
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using
      congrArg (fun k => k.app U.val x) (idealQuotientπ_baseIdealReductionIso_hom f I F h)
  have hz : (Submodule.Quotient.mk x : Γ(F.obj.obj (op m), U) ⧸
      idealQuotientAffineChartSubmodule f (F.obj.obj (op m)) (I ^ n) U) = 0 := by
    apply q.injective
    apply e.injective
    simpa only [map_zero] using hc.trans hx'
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  simpa only [idealQuotientAffineChartSubmodule, idealThickeningIdealSheaf_ideal,
    idealSectionRingHom, Ideal.map_pow] using hm

/-- Compatible algebraic generators that generate the special fibre generate
all stages, including the zero stage. Nilpotent generation replaces any
relative-flatness assumption. -/
theorem formal_compatible_epi_of_special_fibre
    {P : X.Modules} [P.IsQuasicoherent]
    (p : (Functor.const ℕᵒᵖ).obj P ⟶ F.obj) [Epi (p.app (op 1))]
    (n : ℕ) : Epi (p.app (op n)) := by
  apply compatible_epi_of_nilpotent_kernel_bound (idealThickeningIdealSheaf f I)
    F.obj (fun k => inferInstance) p 1
    (fun a b h => F.map_epi h) F.property.annihilated ?_ n
  intro m h U
  simpa only [pow_one] using formalTransition_affine_kernel_le f I F h U

end AlgebraicGeometry.Scheme.Cohomology
