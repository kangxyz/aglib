/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCompatibility
public import Aglib.AlgebraicGeometry.FunctionField.BirationalCharts
public import Aglib.AlgebraicGeometry.Normalization.FiniteFunctionField.ChartSectionsTransport
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover.Nagata


/-!
# AlgebraicGeometry / Surfaces / Birational / NormalizedBlowupCover / ChartSections

Source: `NormalizedChartSections/Core.lean`.
Incoming SHA256: `f4dd17e6760d9a9636a67bded2c6d1480493561b6fb45acdbc9d0a6220f3dad5`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover

universe u vK vL


open AlgebraicGeometry.Scheme.FunctionField.BirationalCharts

namespace AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.ChartSections


section ModelField

variable (A : CommRingCat.{u}) [IsDomain A]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} [IsIntegral X]
  (β : X ⟶ Spec A) [IsDominant β]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))


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
/-- The SAME Cover action, through the original birational inverse, reaches original L. -/
theorem modelFunctionFieldEquiv_extension :
    letI := Cover.Nagata.fieldAlgebra β hβ s
    (affineFunctionFieldEquiv B L).toRingHom.comp
        (algebraMap X.functionField (Spec B).functionField) =
      (algebraMap K L).comp (modelFunctionFieldEquiv A K β hβ).toRingHom := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  change (affineFunctionFieldEquiv B L).toRingHom.comp
    ((Scheme.functionFieldMap s).comp (Cover.baseFieldIso β hβ).inv.hom) = _
  rw [← RingHom.comp_assoc, affineFunctionFieldEquiv_extension A B K L s hs,
    RingHom.comp_assoc]
  rfl


include hs in
/-- Whole original ambient-field compatibility on a chart, before algebra upgrade. -/
theorem chartExtensionMap_eq (U : X.Opens) [Nonempty U] :
    letI := Cover.Nagata.fieldAlgebra β hβ s
    letI := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
    (affineFunctionFieldEquiv B L).toRingHom.comp
        (algebraMap Γ(X, U) (Spec B).functionField) =
      chartExtensionMap A K L β hβ U := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  change (affineFunctionFieldEquiv B L).toRingHom.comp
    ((algebraMap X.functionField (Spec B).functionField).comp
      (X.germToFunctionField U).hom) = _
  rw [← RingHom.comp_assoc, modelFunctionFieldEquiv_extension A B K L β hβ s hs]
  rfl

/-- The SAME eF ring equivalence upgraded by the proved original chart square.
There is no R_U-to-B map and no restriction of its B-algebra structure. -/
def chartExtensionFieldEquiv (U : X.Opens) [Nonempty U] :
    letI := Cover.Nagata.fieldAlgebra β hβ s
    letI := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (Spec B).functionField ≃ₐ[Γ(X, U)] L := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  exact
    { (affineFunctionFieldEquiv B L).toRingEquiv with
      commutes' := fun r => RingHom.congr_fun (chartExtensionMap_eq A B K L β hβ s hs U) r }

/-- The chart algebra upgrade has exactly the original eF ring equivalence. -/
@[simp]
theorem chartExtensionFieldEquiv_toRingEquiv (U : X.Opens) [Nonempty U] :
    letI := Cover.Nagata.fieldAlgebra β hβ s
    letI := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (chartExtensionFieldEquiv A B K L β hβ s hs U).toRingEquiv =
      (affineFunctionFieldEquiv B L).toRingEquiv := rfl

/-- The chart algebra upgrade has exactly the original eF whole function. -/
theorem chartExtensionFieldEquiv_coe (U : X.Opens) [Nonempty U] :
    letI := Cover.Nagata.fieldAlgebra β hβ s
    letI := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (chartExtensionFieldEquiv A B K L β hβ s hs U : (Spec B).functionField → L) =
      affineFunctionFieldEquiv B L := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  exact
    (AlgEquiv.coe_ringEquiv (chartExtensionFieldEquiv A B K L β hβ s hs U)).symm.trans
      ((congrArg (fun q : (Spec B).functionField ≃+* L =>
          (q : (Spec B).functionField → L))
        (chartExtensionFieldEquiv_toRingEquiv A B K L β hβ s hs U)).trans
          (AlgEquiv.coe_ringEquiv (affineFunctionFieldEquiv B L)))


end OriginalCoverField

section CoverCharts

variable {A B : CommRingCat.{u}} [IsDomain A] [IsDomain B] [Algebra A B]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type vL) [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  {X : Scheme.{u}} [IsIntegral X]
  (β : X ⟶ Spec A) [IsDominant β]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (s : Spec B ⟶ Spec A) [IsDominant s]
  (hs : s = Spec.map (CommRingCat.ofHom (algebraMap A B)))

omit [Algebra A B] in
/-- Affineness is derived for the SAME original relative-normalization map. -/
theorem coverPi_isAffineHom : IsAffineHom (Cover.pi β hβ s) :=
  inferInstanceAs (IsAffineHom (Cover.genericMap β hβ s).fromNormalization)

attribute [local instance] coverPi_isAffineHom

/-- Original generic-chart sections in the SAME actual Cover field. -/
def coverChartFieldIso (U : X.Opens) [Nonempty U] :
    Γ(Spec (Spec B).functionField, (Cover.genericMap β hβ s) ⁻¹ᵁ U) ≅
      (Spec B).functionField := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  exact FiniteFunctionField.chartFieldIsoOfEq X (Spec B).functionField
    (Cover.genericMap β hβ s) (Cover.Nagata.genericMap_eq β hβ s) U

include hs in
/-- Sections on the SAME actual Cover normalization in the literal closure in original L. -/
def normalizedChartSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((Cover.pi β hβ s).app U).hom.toAlgebra
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    Γ(Cover.normalization β hβ s, (Cover.pi β hβ s) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) L := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  let : Algebra Γ(X, U)
      Γ(Cover.normalization β hβ s, (Cover.pi β hβ s) ⁻¹ᵁ U) :=
    ((Cover.pi β hβ s).app U).hom.toAlgebra
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  exact FiniteFunctionField.normalizationSectionsEquivMapOfEq X (Spec B).functionField
    (Cover.genericMap β hβ s) (Cover.Nagata.genericMap_eq β hβ s) U hU L
    (chartExtensionFieldEquiv A B K L β hβ s hs U)

/-- The original chart coordinate has the SAME whole function as its mapped constructor. -/
theorem normalizedChartSectionsEquiv_coe
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := Cover.Nagata.fieldAlgebra β hβ s
    letI := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
    letI := ((Cover.pi β hβ s).app U).hom.toAlgebra
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (normalizedChartSectionsEquiv K L β hβ s hs U hU :
      Γ(Cover.normalization β hβ s, (Cover.pi β hβ s) ⁻¹ᵁ U) →
        integralClosure Γ(X, U) L) =
      (FiniteFunctionField.normalizationSectionsEquivMapOfEq X (Spec B).functionField
        (Cover.genericMap β hβ s) (Cover.Nagata.genericMap_eq β hβ s) U hU L
        (chartExtensionFieldEquiv A B K L β hβ s hs U) :
      Γ(Cover.normalization β hβ s, (Cover.pi β hβ s) ⁻¹ᵁ U) →
        integralClosure Γ(X, U) L) := by rfl

/-- The original pi section map becomes the literal closure coefficient inclusion. -/
theorem normalizedChartSectionsEquiv_coefficients
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (normalizedChartSectionsEquiv K L β hβ s hs U hU).toRingHom.comp
        ((Cover.pi β hβ s).app U).hom =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) L) := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  let := ((Cover.pi β hβ s).app U).hom.toAlgebra
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  have hNative := FiniteFunctionField.normalizationSectionsEquivMapOfEq_coefficients
    X (Spec B).functionField (Cover.genericMap β hβ s)
    (Cover.Nagata.genericMap_eq β hβ s) U hU L
    (chartExtensionFieldEquiv A B K L β hβ s hs U)
  dsimp only [normalizedChartSectionsEquiv, Cover.normalization, Cover.pi] at hNative ⊢
  exact hNative

/-- The whole ambient map retains the SAME original eta and original affine field comparison. -/
theorem normalizedChartSectionsEquiv_val_comp
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (integralClosure Γ(X, U) L).val.toRingHom.comp
        (normalizedChartSectionsEquiv K L β hβ s hs U hU).toRingHom =
      (affineFunctionFieldEquiv B L).toRingHom.comp
        ((coverChartFieldIso β hβ s U).hom.hom.comp
          ((Cover.eta β hβ s).appLE ((Cover.pi β hβ s) ⁻¹ᵁ U)
            ((Cover.genericMap β hβ s) ⁻¹ᵁ U) (by
              simp only [← Scheme.Hom.comp_preimage, Cover.eta_pi, le_refl])).hom) := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  have hNative := FiniteFunctionField.normalizationSectionsEquivMapOfEq_val_comp
    X (Spec B).functionField
    (Cover.genericMap β hβ s) (Cover.Nagata.genericMap_eq β hβ s) U hU L
      (chartExtensionFieldEquiv A B K L β hβ s hs U)
  have hFieldMap : (chartExtensionFieldEquiv A B K L β hβ s hs U).toRingHom =
      (affineFunctionFieldEquiv B L).toRingHom :=
    congrArg RingEquiv.toRingHom
      (chartExtensionFieldEquiv_toRingEquiv A B K L β hβ s hs U)
  dsimp only [normalizedChartSectionsEquiv, coverChartFieldIso, Cover.normalization,
    Cover.pi, Cover.eta] at hNative ⊢
  simp only [hFieldMap] at hNative ⊢
  exact hNative

/-- All actual nonempty affine restrictions become inclusions of closures in the SAME L. -/
theorem normalizedChartSectionsEquiv_restriction
    (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    letI := (chartExtensionMap A K L β hβ V).toAlgebra
    letI := chartExtensionRestriction_isScalarTower A K L β hβ U V h
    (normalizedChartSectionsEquiv K L β hβ s hs V hV).toRingHom.comp
        ((Cover.normalization β hβ s).presheaf.map
          (homOfLE ((Cover.pi β hβ s).preimage_mono h)).op).hom =
      (integralClosure.scalarExtensionHom Γ(X, U) Γ(X, V) L).toRingHom.comp
        (normalizedChartSectionsEquiv K L β hβ s hs U hU).toRingHom := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField U
  let := FiniteFunctionField.chartAmbientAlgebra X (Spec B).functionField V
  let := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let := FiniteFunctionField.chartAmbientRestriction_isScalarTower
    X (Spec B).functionField U V h
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  let := (chartExtensionMap A K L β hβ V).toAlgebra
  let := chartExtensionRestriction_isScalarTower A K L β hβ U V h
  have hEU : (chartExtensionFieldEquiv A B K L β hβ s hs U).toRingHom =
      (affineFunctionFieldEquiv B L).toRingHom :=
    congrArg RingEquiv.toRingHom
      (chartExtensionFieldEquiv_toRingEquiv A B K L β hβ s hs U)
  have hEV : (chartExtensionFieldEquiv A B K L β hβ s hs V).toRingHom =
      (affineFunctionFieldEquiv B L).toRingHom :=
    congrArg RingEquiv.toRingHom
      (chartExtensionFieldEquiv_toRingEquiv A B K L β hβ s hs V)
  have hE := hEU.trans hEV.symm
  have hNative := FiniteFunctionField.normalizationSectionsEquivMapOfEq_restriction
    X (Spec B).functionField (Cover.genericMap β hβ s)
    (Cover.Nagata.genericMap_eq β hβ s) U V h hU hV L
    (chartExtensionFieldEquiv A B K L β hβ s hs U)
    (chartExtensionFieldEquiv A B K L β hβ s hs V)
    (chartExtensionRestriction_isScalarTower A K L β hβ U V h) hE
  dsimp only [normalizedChartSectionsEquiv, Cover.normalization, Cover.pi] at hNative ⊢
  exact hNative

omit [Algebra A B] in
/-- The actual principal restriction is localization through its original pi coefficients.
The principal subopen may be empty; no field or domain structure is asserted there. -/
theorem normalizedChartSections_isLocalization_basicOpen
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (t : Γ(X, U)) :
    letI := ((Cover.normalization β hβ s).presheaf.map
      (homOfLE ((Cover.pi β hβ s).preimage_mono (X.basicOpen_le t))).op).hom.toAlgebra
    IsLocalization.Away ((Cover.pi β hβ s).app U t)
      Γ(Cover.normalization β hβ s, (Cover.pi β hβ s) ⁻¹ᵁ X.basicOpen t) := by
  let := Cover.Nagata.fieldAlgebra β hβ s
  exact FiniteFunctionField.normalizationSections_isLocalization_basicOpen_of_eq
    X (Spec B).functionField
    (Cover.genericMap β hβ s) (Cover.Nagata.genericMap_eq β hβ s) U hU t

omit [Algebra A B] in
/-- The actual normalization chart and base chart retain their original coefficient square. -/
theorem normalizedChart_coefficientBase {Λ : CommRingCat.{u}} (a : X ⟶ Spec Λ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    (Spec.preimage ((hU.preimage (Cover.pi β hβ s)).fromSpec ≫
      (Cover.pi β hβ s) ≫ a)).hom =
        ((Cover.pi β hβ s).app U).hom.comp (Spec.preimage (hU.fromSpec ≫ a)).hom := by
  have he : Spec.map ((Cover.pi β hβ s).app U) ≫ hU.fromSpec =
      (hU.preimage (Cover.pi β hβ s)).fromSpec ≫ Cover.pi β hβ s := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      (IsAffineOpen.SpecMap_appLE_fromSpec (Cover.pi β hβ s) hU
        (hU.preimage (Cover.pi β hβ s)) le_rfl)
  have hp := congrArg (fun f : Spec Γ(Cover.normalization β hβ s,
      (Cover.pi β hβ s) ⁻¹ᵁ U) ⟶ Spec Λ => Spec.preimage f)
    (congrArg (fun f => f ≫ a) he)
  simp only [Category.assoc] at hp
  rw [Spec.preimage_comp, Spec.preimage_map] at hp
  exact (congrArg CommRingCat.Hom.hom hp).symm

/-- The completed normalization chart comparison retains the actual coefficient-base map. -/
theorem normalizedChartSectionsEquiv_coefficientBase {Λ : CommRingCat.{u}}
    (a : X ⟶ Spec Λ) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (normalizedChartSectionsEquiv K L β hβ s hs U hU).toRingHom.comp
        (Spec.preimage ((hU.preimage (Cover.pi β hβ s)).fromSpec ≫
          (Cover.pi β hβ s) ≫ a)).hom =
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)).comp
        (Spec.preimage (hU.fromSpec ≫ a)).hom := by
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  rw [normalizedChart_coefficientBase, ← RingHom.comp_assoc,
    normalizedChartSectionsEquiv_coefficients]

/-- The actual normalization chart's coefficient map reaches the ORIGINAL Lambda-to-L map. -/
theorem normalizedChartSectionsEquiv_coefficientBase_ambient {Λ : CommRingCat.{u}}
    (ρ : Λ ⟶ A) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (chartExtensionMap A K L β hβ U).toAlgebra
    (algebraMap (integralClosure Γ(X, U) L) L).comp
        ((normalizedChartSectionsEquiv K L β hβ s hs U hU).toRingHom.comp
          (Spec.preimage ((hU.preimage (Cover.pi β hβ s)).fromSpec ≫
            (Cover.pi β hβ s) ≫ (β ≫ Spec.map ρ))).hom) =
      (algebraMap A L).comp ρ.hom := by
  let := (chartExtensionMap A K L β hβ U).toAlgebra
  rw [normalizedChartSectionsEquiv_coefficientBase, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq Γ(X, U) (integralClosure Γ(X, U) L) L]
  exact chartExtensionMap_coefficientBase A K L β hβ ρ U hU

end CoverCharts

end AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.ChartSections
