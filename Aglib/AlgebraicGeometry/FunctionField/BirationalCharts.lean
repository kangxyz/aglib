/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCompatibility
public import Aglib.AlgebraicGeometry.FunctionField.Scalars


/-!
# AlgebraicGeometry / FunctionField / BirationalCharts

Source: `NormalizedChartSections/Core.lean`.
Incoming SHA256: `f4dd17e6760d9a9636a67bded2c6d1480493561b6fb45acdbc9d0a6220f3dad5`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u vK vL


open AlgebraicGeometry.Scheme.FunctionField

namespace AlgebraicGeometry.Scheme.FunctionField.BirationalCharts

/-- The native affine function field compared with the original supplied fraction field. -/
def affineFunctionFieldEquiv (A : CommRingCat.{u}) [IsDomain A]
    (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K] :
    (Spec A).functionField ≃ₐ[A] K :=
  IsLocalization.algEquiv A⁰ (Spec A).functionField K

section ModelField

variable (A : CommRingCat.{u}) [IsDomain A]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} [IsIntegral X]
  (β : X ⟶ Spec A) [IsDominant β]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))

include hβ in
/-- The original inverse birational field map, followed by the native fraction comparison. -/
def modelFunctionFieldEquiv :
    letI := (genericScalar β).hom.toAlgebra
    X.functionField ≃ₐ[A] K := by
  let := (genericScalar β).hom.toAlgebra
  let q := (@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap β)) hβ)
  let e := affineFunctionFieldEquiv A K
  refine
    { toRingEquiv := q.symm.commRingCatIsoToRingEquiv.trans e.toRingEquiv
      commutes' := ?_ }
  intro a
  change e (q.inv (genericScalar β a)) = algebraMap A K a
  rw [ConcreteCategory.congr_hom (genericScalar_eq_functionFieldMap β) a]
  change e (q.inv (q.hom (algebraMap A (Spec A).functionField a))) = _
  have hi : q.inv (q.hom (algebraMap A (Spec A).functionField a)) =
      algebraMap A (Spec A).functionField a :=
    ConcreteCategory.congr_hom q.hom_inv_id _
  exact (congrArg e hi).trans (e.commutes a)

/-- The comparison cancels the SAME original birational field map. -/
theorem modelFunctionFieldEquiv_comp :
    (modelFunctionFieldEquiv A K β hβ).toRingHom.comp (Scheme.functionFieldMap β) =
      (affineFunctionFieldEquiv A K).toRingHom := by
  apply RingHom.ext
  intro x
  change affineFunctionFieldEquiv A K
    (((@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap β)) hβ)).inv
      (((@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap β)) hβ)).hom x)) = _
  have hi : ((@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap β)) hβ)).inv
      (((@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap β)) hβ)).hom x) = x :=
    ConcreteCategory.congr_hom ((@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap β)) hβ)).hom_inv_id x
  exact congrArg (affineFunctionFieldEquiv A K) hi

/-- Original affine base scalars become their originally supplied fraction inclusion. -/
theorem modelFunctionFieldEquiv_coefficients :
    (modelFunctionFieldEquiv A K β hβ).toRingHom.comp (genericScalar β).hom =
      algebraMap A K := by
  let := (genericScalar β).hom.toAlgebra
  apply RingHom.ext
  intro a
  exact (modelFunctionFieldEquiv A K β hβ).commutes a

/-- The original nonempty chart germ followed by the SAME model-field comparison. -/
def chartFractionMap (U : X.Opens) [Nonempty U] : Γ(X, U) →+* K :=
  (modelFunctionFieldEquiv A K β hβ).toRingHom.comp (X.germToFunctionField U).hom

/-- The original chart's actual fraction field is the originally supplied K. -/
theorem chartFractionMap_isFractionRing (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := (chartFractionMap A K β hβ U).toAlgebra
    IsFractionRing Γ(X, U) K := by
  let := (chartFractionMap A K β hβ U).toAlgebra
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let := (genericScalar β).hom.toAlgebra
  let e : X.functionField ≃ₐ[Γ(X, U)] K :=
    { (modelFunctionFieldEquiv A K β hβ).toRingEquiv with commutes' := fun _ => rfl }
  exact IsFractionRing.of_algEquiv e

omit [IsDomain A] [IsDominant β] in
/-- The actual affine-chart coefficient map commutes with its original generic germ. -/
theorem chartGerm_coefficients (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (Spec.preimage (hU.fromSpec ≫ β)).hom =
      (genericScalar β).hom := by
  have hg : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hγ : Spec.map (X.germToFunctionField U) ≫ hU.fromSpec =
      X.fromSpecStalk (genericPoint X) :=
    hU.fromSpecStalk_eq_fromSpecStalk hg
  have he : Spec.preimage (Spec.map (X.germToFunctionField U) ≫ (hU.fromSpec ≫ β)) =
      genericScalar β := by
    rw [← Category.assoc, hγ]
    rfl
  rw [Spec.preimage_comp, Spec.preimage_map] at he
  exact congrArg CommRingCat.Hom.hom he

/-- Original chart coefficients, not a selected replacement algebra, map into original K. -/
theorem chartFractionMap_coefficients (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (chartFractionMap A K β hβ U).comp (Spec.preimage (hU.fromSpec ≫ β)).hom =
      algebraMap A K := by
  rw [chartFractionMap, RingHom.comp_assoc, chartGerm_coefficients]
  exact modelFunctionFieldEquiv_coefficients A K β hβ

/-- The original affine base map and supplied K-action form their derived scalar tower. -/
theorem chartFractionMap_isScalarTower (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (Spec.preimage (hU.fromSpec ≫ β)).hom.toAlgebra
    letI := (chartFractionMap A K β hβ U).toAlgebra
    IsScalarTower A Γ(X, U) K := by
  let := (Spec.preimage (hU.fromSpec ≫ β)).hom.toAlgebra
  let := (chartFractionMap A K β hβ U).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (RingHom.congr_fun (chartFractionMap_coefficients A K β hβ U hU) a).symm

/-- Changing the coefficient base retains the original rho and actual Spec.preimage. -/
theorem chartFractionMap_coefficientBase {Λ : CommRingCat.{u}} (ρ : Λ ⟶ A)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (chartFractionMap A K β hβ U).comp
        (Spec.preimage (hU.fromSpec ≫ (β ≫ Spec.map ρ))).hom =
      (algebraMap A K).comp ρ.hom := by
  rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp,
    ← RingHom.comp_assoc, chartFractionMap_coefficients]

/-- Every actual nonempty restriction retains the SAME supplied fraction-field map. -/
theorem chartFractionMap_restriction (U V : X.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ U) :
    (chartFractionMap A K β hβ V).comp (X.presheaf.map (homOfLE h).op).hom =
      chartFractionMap A K β hβ U := by
  have hv : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hres : (X.germToFunctionField V).hom.comp
      (X.presheaf.map (homOfLE h).op).hom = (X.germToFunctionField U).hom :=
    congrArg CommRingCat.Hom.hom (X.presheaf.germ_res (homOfLE h) (genericPoint X) hv)
  dsimp only [chartFractionMap]
  rw [RingHom.comp_assoc, hres]

end ModelField

section OriginalCoverField

variable (A B : CommRingCat.{u}) [IsDomain A] [IsDomain B] [Algebra A B]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type vL) [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  {X : Scheme.{u}} [IsIntegral X]
  (β : X ⟶ Spec A) [IsDominant β]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (s : Spec B ⟶ Spec A) [IsDominant s]
  (hs : s = Spec.map (CommRingCat.ofHom (algebraMap A B)))

include hs in
/-- The actual extension field map commutes with both original fraction comparisons. -/
theorem affineFunctionFieldEquiv_extension :
    (affineFunctionFieldEquiv B L).toRingHom.comp (Scheme.functionFieldMap s) =
      (algebraMap K L).comp (affineFunctionFieldEquiv A K).toRingHom := by
  let := Scheme.functionFieldMapAlgebra s
  let : Algebra A (Spec B).functionField :=
    ((algebraMap B (Spec B).functionField).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B (Spec B).functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hc : (Scheme.functionFieldMap s).comp (algebraMap A (Spec A).functionField) =
      (algebraMap B (Spec B).functionField).comp (algebraMap A B) := by
    subst s
    exact FunctionField.AffineCompatibility.fieldMap_spec_constants B A _
  let : IsScalarTower A (Spec A).functionField (Spec B).functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hc a).symm
  apply RingHom.ext
  intro x
  exact (IsFractionRing.algEquiv_commutes
    (affineFunctionFieldEquiv A K) (affineFunctionFieldEquiv B L) x).symm


/-- Original chart scalars in L pass through the original K-to-L map. -/
def chartExtensionMap (U : X.Opens) [Nonempty U] : Γ(X, U) →+* L :=
  (algebraMap K L).comp (chartFractionMap A K β hβ U)

omit [Algebra A L] [IsScalarTower A K L] in
/-- Original chart scalars, K and L form their literal composed scalar tower. -/
theorem chartExtensionMap_isScalarTower (U : X.Opens) [Nonempty U] :
    letI := (chartFractionMap A K β hβ U).toAlgebra
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    IsScalarTower Γ(X, U) K L := by
  let := (chartFractionMap A K β hβ U).toAlgebra
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The original chart coefficients into L retain the original A-to-L algebraMap. -/
theorem chartExtensionMap_coefficients (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (chartExtensionMap A K L β hβ U).comp (Spec.preimage (hU.fromSpec ≫ β)).hom =
      algebraMap A L := by
  rw [chartExtensionMap, RingHom.comp_assoc, chartFractionMap_coefficients,
    ← IsScalarTower.algebraMap_eq A K L]

/-- The original coefficient-base triangle into L retains the original rho. -/
theorem chartExtensionMap_coefficientBase {Λ : CommRingCat.{u}} (ρ : Λ ⟶ A)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (chartExtensionMap A K L β hβ U).comp
        (Spec.preimage (hU.fromSpec ≫ (β ≫ Spec.map ρ))).hom =
      (algebraMap A L).comp ρ.hom := by
  rw [chartExtensionMap, RingHom.comp_assoc, chartFractionMap_coefficientBase,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A K L]


omit [Algebra A L] [IsScalarTower A K L] in
/-- Original nonempty chart restrictions retain the unchanged ambient L. -/
theorem chartExtensionMap_restriction (U V : X.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ U) :
    (chartExtensionMap A K L β hβ V).comp (X.presheaf.map (homOfLE h).op).hom =
      chartExtensionMap A K L β hβ U := by
  rw [chartExtensionMap, RingHom.comp_assoc, chartFractionMap_restriction]
  rfl

omit [Algebra A L] [IsScalarTower A K L] in
/-- The actual chart restriction and original L-actions form their derived scalar tower. -/
theorem chartExtensionRestriction_isScalarTower
    (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    letI := (chartExtensionMap A K L β hβ V).toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) L := by
  let := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  let := (chartExtensionMap A K L β hβ V).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.congr_fun (chartExtensionMap_restriction A K L β hβ U V h) r).symm

end OriginalCoverField


end AlgebraicGeometry.Scheme.FunctionField.BirationalCharts
