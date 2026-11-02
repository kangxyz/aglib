/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FiniteFunctionField
public import Aglib.RingTheory.IntegralClosure.Localization

/-!
# Original normalization sections in the specified generic field

The actual normalization section ring is identified with the literal integral
closure in the same specified field. Original coefficients, the ambient
embedding and every nonempty affine restriction are retained. No finiteness,
Nagata, normality or Noetherian hypothesis is needed for these comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FiniteFunctionField

variable (X : Scheme.{u}) [IsIntegral X]
  (F : Type u) [Field F] [Algebra X.functionField F]

/-- The original chart action on the specified field, through its actual generic germ. -/
@[instance_reducible] def chartAmbientAlgebra (U : X.Opens) [Nonempty U] :
    Algebra Γ(X, U) F :=
  ((algebraMap X.functionField F).comp (X.germToFunctionField U).hom).toAlgebra

attribute [local instance] chartAmbientAlgebra

/-- The specified ambient action retains the original function-field tower. -/
theorem chartAmbient_isScalarTower (U : X.Opens) [Nonempty U] :
    IsScalarTower Γ(X, U) X.functionField F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] chartAmbient_isScalarTower

/-- Actual normalization sections, in the literal closure in the SAME specified field. -/
def normalizationSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((fromNormalization X F).app U).hom.toAlgebra
    Γ(normalization X F, (fromNormalization X F) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) F := by
  let := ((fromNormalization X F).app U).hom.toAlgebra
  let e := ((chartFieldEquiv X F U).restrictScalars Γ(X, U)).mapIntegralClosure
  refine
    { toRingEquiv := ((genericMap X F).normalizationObjIso hU).commRingCatIsoToRingEquiv.trans
        e.toRingEquiv
      commutes' := ?_ }
  intro r
  have hc : (fromNormalization X F).app U ≫
      ((genericMap X F).normalizationObjIso hU).hom =
        CommRingCat.ofHom (algebraMap Γ(X, U)
          (integralClosure Γ(X, U) Γ(Spec (.of F), (genericMap X F) ⁻¹ᵁ U))) := by
    change (genericMap X F).fromNormalization.app U ≫ _ = _
    rw [Scheme.Hom.fromNormalization_app _ hU, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  change e (((genericMap X F).normalizationObjIso hU).hom
    ((fromNormalization X F).app U r)) = algebraMap Γ(X, U) _ r
  exact (congrArg e (ConcreteCategory.congr_hom hc r)).trans (e.commutes r)

/-- The original structural section map becomes the original closure coefficient map. -/
@[reassoc]
theorem normalizationSectionsEquiv_coefficients
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (fromNormalization X F).app U ≫
        CommRingCat.ofHom (normalizationSectionsEquiv X F U hU).toRingHom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) F)) := by
  let := ((fromNormalization X F).app U).hom.toAlgebra
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (normalizationSectionsEquiv X F U hU).commutes r

/-- The whole ambient map is the original normalization section map followed by its field chart. -/
theorem normalizationSectionsEquiv_val_comp
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((fromNormalization X F).app U).hom.toAlgebra
    (integralClosure Γ(X, U) F).val.toRingHom.comp
        (normalizationSectionsEquiv X F U hU).toRingHom =
      (chartFieldIso X F U).hom.hom.comp
        ((toNormalization X F).appLE ((fromNormalization X F) ⁻¹ᵁ U)
          ((genericMap X F) ⁻¹ᵁ U) (by
            simp only [← Scheme.Hom.comp_preimage, toNormalization_fromNormalization,
              le_refl])).hom := by
  let := ((fromNormalization X F).app U).hom.toAlgebra
  apply RingHom.ext
  intro c
  change (chartFieldIso X F U).hom
    ((((genericMap X F).normalizationObjIso hU).hom c :
      integralClosure Γ(X, U) Γ(Spec (.of F), (genericMap X F) ⁻¹ᵁ U)) :
        Γ(Spec (.of F), (genericMap X F) ⁻¹ᵁ U)) = _
  exact congrArg (chartFieldIso X F U).hom
    (ConcreteCategory.congr_hom ((genericMap X F).normalizationObjIso_hom_val hU) c)

/-- The closure coordinate has exactly the original ambient section value. -/
theorem normalizationSectionsEquiv_val
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (c : Γ(normalization X F, (fromNormalization X F) ⁻¹ᵁ U)) :
    (normalizationSectionsEquiv X F U hU c : F) =
      (chartFieldIso X F U).hom
        ((toNormalization X F).appLE ((fromNormalization X F) ⁻¹ᵁ U)
          ((genericMap X F) ⁻¹ᵁ U) (by
            simp only [← Scheme.Hom.comp_preimage, toNormalization_fromNormalization,
              le_refl]) c) := by
  let := ((fromNormalization X F).app U).hom.toAlgebra
  exact RingHom.congr_fun (normalizationSectionsEquiv_val_comp X F U hU) c

section Restriction

variable (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)

/-- Original generic-section restrictions become the identity on the specified field. -/
@[reassoc]
theorem chartFieldIso_restriction :
    (Spec (.of F)).presheaf.map (homOfLE ((genericMap X F).preimage_mono h)).op ≫
        (chartFieldIso X F V).hom =
      (chartFieldIso X F U).hom := by
  simp only [chartFieldIso, chartOriginalSectionsIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom]
  rw [← Functor.map_comp_assoc]
  congr 1

/-- The original chart restriction and generic actions form their actual scalar tower. -/
theorem chartAmbientRestriction_isScalarTower :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) F := by
  let := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap X.functionField F (X.germToFunctionField U r) =
    algebraMap X.functionField F
      (X.germToFunctionField V (X.presheaf.map (homOfLE h).op r))
  have hv : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  exact congrArg (algebraMap X.functionField F)
    (ConcreteCategory.congr_hom (X.presheaf.germ_res (homOfLE h) (genericPoint X) hv) r).symm

/-- Every actual affine restriction becomes the same-ambient inclusion of closures. -/
theorem normalizationSectionsEquiv_restriction
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI := chartAmbientRestriction_isScalarTower X F U V h
    (normalizationSectionsEquiv X F V hV).toRingHom.comp
        ((normalization X F).presheaf.map
          (homOfLE ((fromNormalization X F).preimage_mono h)).op).hom =
      (integralClosure.scalarExtensionHom Γ(X, U) Γ(X, V) F).toRingHom.comp
        (normalizationSectionsEquiv X F U hU).toRingHom := by
  let := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let := chartAmbientRestriction_isScalarTower X F U V h
  have he : (normalization X F).presheaf.map
        (homOfLE ((fromNormalization X F).preimage_mono h)).op ≫
      (toNormalization X F).appLE ((fromNormalization X F) ⁻¹ᵁ V)
        ((genericMap X F) ⁻¹ᵁ V) (by
          simp only [← Scheme.Hom.comp_preimage, toNormalization_fromNormalization,
            le_refl]) =
    (toNormalization X F).appLE ((fromNormalization X F) ⁻¹ᵁ U)
        ((genericMap X F) ⁻¹ᵁ U) (by
          simp only [← Scheme.Hom.comp_preimage, toNormalization_fromNormalization,
            le_refl]) ≫
      (Spec (.of F)).presheaf.map (homOfLE ((genericMap X F).preimage_mono h)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  apply RingHom.ext
  intro c
  apply Subtype.ext
  change (normalizationSectionsEquiv X F V hV
    ((normalization X F).presheaf.map
      (homOfLE ((fromNormalization X F).preimage_mono h)).op c) : F) =
        (normalizationSectionsEquiv X F U hU c : F)
  rw [normalizationSectionsEquiv_val, normalizationSectionsEquiv_val]
  exact (congrArg (chartFieldIso X F V).hom (ConcreteCategory.congr_hom he c)).trans
    (ConcreteCategory.congr_hom (chartFieldIso_restriction X F U V h) _)

end Restriction

/-- The original normalization section restriction over a principal base open
is localization, through its actual affine preimage and section map. -/
theorem normalizationSections_isLocalization_basicOpen
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (t : Γ(X, U)) :
    letI := ((normalization X F).presheaf.map
      (homOfLE ((fromNormalization X F).preimage_mono (X.basicOpen_le t))).op).hom.toAlgebra
    IsLocalization.Away ((fromNormalization X F).app U t)
      Γ(normalization X F, (fromNormalization X F) ⁻¹ᵁ X.basicOpen t) := by
  let := ((normalization X F).presheaf.map
    (homOfLE ((fromNormalization X F).preimage_mono (X.basicOpen_le t))).op).hom.toAlgebra
  exact (hU.preimage (fromNormalization X F)).isLocalization_of_eq_basicOpen
    ((fromNormalization X F).app U t)
    (homOfLE ((fromNormalization X F).preimage_mono (X.basicOpen_le t)))
    ((fromNormalization X F).preimage_basicOpen t)

end AlgebraicGeometry.Scheme.FiniteFunctionField
