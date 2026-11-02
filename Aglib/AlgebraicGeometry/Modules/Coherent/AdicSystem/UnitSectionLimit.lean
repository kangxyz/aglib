/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.UnitSectionComparison
public import Aglib.AlgebraicGeometry.Spec.AdicSectionCone
public import Aglib.CategoryTheory.Limits.Types.SurjectiveConeComparison
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits

/-! # The original module-unit cone from actual ring-section completeness

The original stage equivalences retain both unit maps. Surjectivity of these
original section maps supplies their complete transition law, after which
native forgetful preservation and reflection transfer the limit property.
No ring is assigned to a module quotient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- Transfer the actual ring cone to the unchanged ideal-sheaf module-unit cone. -/
theorem idealSheafUnitSectionCone_isLimit_of_ringCone
    (hR : IsLimit (adicRingSectionCone f I))
    (hsurj : ∀ n, Function.Surjective ((idealThickeningι f (I ^ n)).appTop)) :
    Nonempty (IsLimit (idealSheafSectionCone X (idealThickeningIdealSheaf f I)
      (SheafOfModules.unit X.ringCatSheaf))) := by
  let c := idealSheafSectionCone X (idealThickeningIdealSheaf f I)
    (SheafOfModules.unit X.ringCatSheaf)
  let U := CategoryTheory.forget (ModuleCat.{u} Γ(X, ⊤))
  let V := CategoryTheory.forget CommRingCat.{u}
  let cF := U.mapCone c
  let cG := V.mapCone (adicRingSectionCone f I)
  let e₀ : cF.pt ≃ cG.pt := Equiv.refl _
  let e (n : ℕᵒᵖ) :
      (idealSheafSectionDiagram X (idealThickeningIdealSheaf f I)
        (SheafOfModules.unit X.ringCatSheaf) ⋙ U).obj n ≃
        (adicRingSectionDiagram f I ⋙ V).obj n := idealSheafUnitSectionEquiv f I n.unop
  have hleg (n : ℕᵒᵖ) (x : cF.pt) :
      e n (cF.π.app n x) = cG.π.app n (e₀ x) :=
    idealSheafUnitSectionEquiv_unit f I n.unop x
  have hs (n : ℕᵒᵖ) : Function.Surjective (cF.π.app n) := by
    intro z
    obtain ⟨x, hx⟩ := hsurj n.unop (e n z)
    refine ⟨e₀.symm x, ?_⟩
    apply (e n).injective
    exact (hleg n (e₀.symm x)).trans hx
  have hG := isLimitOfPreserves V hR
  obtain ⟨hF⟩ := Types.isLimit_of_surjective_cone_comparison cF cG e₀ e hleg hs hG
  let := reflectsLimit_of_reflectsIsomorphisms
    (idealSheafSectionDiagram X (idealThickeningIdealSheaf f I)
      (SheafOfModules.unit X.ringCatSheaf)) U
  exact ⟨isLimitOfReflects U hF⟩

/-- Bijective original quotient scalars make every original restriction section map surjective. -/
theorem adicRingSectionLeg_surjective
    (hb : ∀ n, Function.Bijective (adicSectionScalar f I n)) (n : ℕ) :
    Function.Surjective ((idealThickeningι f (I ^ n)).appTop) := by
  intro y
  obtain ⟨q, hq⟩ := (hb n).surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨affineScalarMap f a, ?_⟩
  have h := affineScalarMap_square (idealThickeningι f (I ^ n))
    (idealThickeningStructure f (I ^ n)) f (Ideal.Quotient.mk (I ^ n))
    pullback.condition
  exact (RingHom.congr_fun h a).trans hq

/-- Original adic scalar completeness gives the actual module-unit limit cone. -/
theorem idealSheafUnitSectionCone_isLimit_of_adicScalars [IsAdicComplete I A]
    (hb : ∀ n, Function.Bijective (adicSectionScalar f I n))
    (hA : Function.Bijective (affineScalarMap f)) :
    Nonempty (IsLimit (idealSheafSectionCone X (idealThickeningIdealSheaf f I)
      (SheafOfModules.unit X.ringCatSheaf))) :=
  idealSheafUnitSectionCone_isLimit_of_ringCone f I
    (adicRingSectionConeIsLimit f I hb hA) (adicRingSectionLeg_surjective f I hb)

end AlgebraicGeometry.Scheme.Modules.Coherent
