/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.FunctionField
public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.StalkMap
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.Etale.ZariskiNagataPurity
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Zariski–Nagata purity for finite dominant integral morphisms

A finite dominant morphism from an integral scheme with normal stalks to a
locally Noetherian integral scheme with regular stalks is etale if its actual
function-field extension is separable and its original stalk map is formally
unramified at every source point of coheight one.

The proof applies algebraic purity to the full inverse image of each nonempty
affine target chart. The chart fraction fields and scalar maps are the actual
scheme function fields and generic germs. Empty charts are handled separately.
Generic separability is retained, including when the height-one condition is
vacuous. No characteristic, equicharacteristic, flatness or dimension bound is
assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsFinite f] [IsDominant f] [IsLocallyNoetherian Y]

/-- Purity on the actual section map of a nonempty affine target chart. -/
theorem etale_app_of_unramified_coheight_one_of_regularStalks
    (hX : X.NormalStalks) (hY : Y.RegularStalks)
    (hsep : letI := Scheme.functionFieldMapAlgebra f
      Algebra.IsSeparable Y.functionField X.functionField)
    (hunram : ∀ x : X, Order.coheight x = 1 →
      (f.stalkMap x).hom.FormallyUnramified)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (f.app U).hom.Etale := by
  let := LocalNormAlgebra.chartAlgebra f U
  let := LocalNormAlgebra.chart_finite f U hU
  let := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := hY.isRegularRing_sections hU
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let := Scheme.isIntegrallyClosed_sections_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  let := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  let := f.chartFunctionFieldAlgebra U
  let := f.chartFractionRingFunctionFieldAlgebra U hU
  let := f.chartFunctionField_source_scalarTower U
  let := f.chartFractionRingFunctionField_scalarTower U hU
  let := f.chartFractionRingFunctionField_isSeparable U hU hsep
  have hchart : Algebra.Etale Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    apply Algebra.etale_of_unramified_height_one_of_isRegularRing
      Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField
    intro q hq
    let hV := hU.preimage f
    obtain ⟨x, rfl⟩ := hV.isoSpec.hom.surjective q
    have hx : Order.coheight x.1 = 1 := by
      rw [← hV.fromSpec_primeIdealOf x,
        coheight_eq_of_isOpenImmersion hV.fromSpec, ← idealHeight_eq_coheight]
      exact hq
    have hlocal := (f.isUnramifiedAt_iff_stalkMap_formallyUnramified
      U hU (f ⁻¹ᵁ U) hV le_rfl x).mpr (hunram x.1 hx)
    rw [Scheme.Hom.appLE_eq_app] at hlocal
    exact hlocal
  exact RingHom.etale_algebraMap.mpr hchart

/-- Zariski–Nagata purity for a finite dominant morphism of integral schemes.
Both generic separability and codimension-one unramifiedness concern the
original morphism. There is no dimension or characteristic restriction. -/
theorem etale_of_unramified_coheight_one_of_regularStalks
    (hX : X.NormalStalks) (hY : Y.RegularStalks)
    (hsep : letI := Scheme.functionFieldMapAlgebra f
      Algebra.IsSeparable Y.functionField X.functionField)
    (hunram : ∀ x : X, Order.coheight x = 1 →
      (f.stalkMap x).hom.FormallyUnramified) : Etale f := by
  classical
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y)
  intro U
  by_cases hne : Nonempty U.1
  · let := hne
    let : IsAffine U.1 := U.2
    let : IsAffine (f ⁻¹ᵁ U.1) := U.2.preimage f
    rw [← f.resLE_eq_morphismRestrict (U := U.1)]
    apply HasRingHomProperty.iff_of_isAffine.mpr
    apply (RingHom.Etale.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U.1 (f ⁻¹ᵁ U.1) le_rfl)).mpr
    simpa only [Scheme.Hom.appLE_eq_app] using
      f.etale_app_of_unramified_coheight_one_of_regularStalks hX hY hsep hunram U.1 U.2
  · let : IsEmpty U.1 := not_nonempty_iff.mp hne
    infer_instance

/-- The equivalent local-ring dimension formulation uses the original source
stalks and retains separability of the original function-field extension. -/
theorem etale_of_unramified_stalk_dimension_one_of_regularStalks
    (hX : X.NormalStalks) (hY : Y.RegularStalks)
    (hsep : letI := Scheme.functionFieldMapAlgebra f
      Algebra.IsSeparable Y.functionField X.functionField)
    (hunram : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified) : Etale f := by
  apply f.etale_of_unramified_coheight_one_of_regularStalks hX hY hsep
  intro x hx
  apply hunram x
  simp only [ringKrullDim_stalk_eq_coheight, hx, WithBot.coe_one]

end AlgebraicGeometry.Scheme.Hom
