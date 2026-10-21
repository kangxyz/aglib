/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Stalk pullbacks of generic finite-etale normalization

The pullback of the actual relative normalization to a target stalk is the spectrum
of that stalk's literal integral closure in the original chart algebra. Localization
of integral closure and the existing normalization chart square construct the map,
cartesian square and comparison isomorphism. No regularity or etaleness is assumed.

Extraction source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.LocalPullback`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, lines 42–184, SHA-256
`9ae9b255d05ff3194bcdf7ee2241a9335d5361cc858a6d6acdfef9c6582f26e0`.
Native relative normalization and its actual chart maps replace source wrappers.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.LocalComparison

universe u

section Algebra

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- The canonical inclusion between integral closures in the same ambient algebra. -/
def closureBaseChangeMap : integralClosure R A →ₐ[R] integralClosure S A :=
  ((integralClosure R A).val).codRestrict ((integralClosure S A).restrictScalars R)
    (fun b => b.2.tower_top)

/-- The smaller integral closure acts through its canonical inclusion into the larger one. -/
instance closureBaseChangeAlgebra :
    Algebra (integralClosure R A) (integralClosure S A) :=
  (closureBaseChangeMap R S A).toRingHom.toAlgebra

/-- Both closure inclusions into the original ambient algebra form a scalar tower. -/
instance closureBaseChangeTower :
    IsScalarTower (integralClosure R A) (integralClosure S A) A :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The closure inclusion respects the original base algebra structures. -/
instance closureBaseChangeBaseTower :
    IsScalarTower R (integralClosure R A) (integralClosure S A) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  rfl

/-- Integral closure commutes with this localization when its denominators act invertibly
in the original ambient algebra. -/
theorem localClosure_isLocalization (M : Submonoid R) [IsLocalization M S]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) A] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R A) M)
      (integralClosure S A) :=
  IsLocalization.integralClosure M

/-- Spectra of these literal integral closures form the localization pullback square. -/
theorem localClosure_isPullback (M : Submonoid R) [IsLocalization M S]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) A] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R A) (integralClosure S A))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (integralClosure S A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let := localClosure_isLocalization R S A M
  have : Algebra.IsPushout R (integralClosure R A) S (integralClosure S A) :=
    Algebra.isPushout_of_isLocalization M S (integralClosure R A) (integralClosure S A)
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ..)

end Algebra

section ActualStalk

variable (X : Scheme.{u}) [IsIntegral X] (C : Scheme.FiniteEtale (Spec X.functionField))
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (y : U)

/-- The target stalk acts on the original chart algebra through its actual function field. -/
instance stalkOriginalAlgebra : Algebra (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫
    X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)) :=
  ((chartFunctionFieldMap X C U).hom.comp
    (algebraMap (X.presheaf.stalk y) X.functionField)).toAlgebra

/-- The stalk action factors through the function-field action on the original chart algebra. -/
instance stalkOriginalFieldTower :
    IsScalarTower (X.presheaf.stalk y) X.functionField (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
        (genericPoint X)) ⁻¹ᵁ U)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Chart sections, the actual target stalk and the original chart algebra form a scalar tower. -/
instance chartStalkOriginalTower :
    IsScalarTower Γ(X, U) (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
        (genericPoint X)) ⁻¹ᵁ U)) := by
  apply IsScalarTower.of_algebraMap_eq'
  change algebraMap Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)) =
    ((algebraMap X.functionField (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ
        U))).comp
      (algebraMap (X.presheaf.stalk y) X.functionField)).comp
        (algebraMap Γ(X, U) (X.presheaf.stalk y))
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Γ(X, U) (X.presheaf.stalk y)
    X.functionField, ← IsScalarTower.algebraMap_eq Γ(X, U) X.functionField (Γ(C.obj.left, (C.obj.hom
        ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))]

/-- Every denominator outside the actual affine prime is already invertible in the
original generic algebra, supplying the second integral-closure localization hypothesis. -/
theorem originalAlgebra_atPrime_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
        (genericPoint X)) ⁻¹ᵁ U))
      (hU.primeIdealOf y).asIdeal.primeCompl) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
          (genericPoint X)) ⁻¹ᵁ U)) := by
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  apply IsLocalization.of_le_isUnit
  rintro _ ⟨r, hr, rfl⟩
  change IsUnit (algebraMap Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X))
      ⁻¹ᵁ U)) r)
  rw [IsScalarTower.algebraMap_apply Γ(X, U) X.functionField (Γ(C.obj.left, (C.obj.hom ≫
      X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))]
  have hr0 : r ∈ Γ(X, U)⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro he
    exact hr (he ▸ (hU.primeIdealOf y).asIdeal.zero_mem)
  exact (IsLocalization.map_units X.functionField ⟨r, hr0⟩).map
    (algebraMap X.functionField (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ
        U)))

/-- The map from the literal stalk integral closure to the original cover's actual
relative normalization, through its actual affine normalization chart. -/
def localToNormalization :
    Spec (.of (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
        (genericPoint X)) ⁻¹ᵁ U)))) ⟶
      (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization :=
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫
      X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)))
    (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint
        X)) ⁻¹ᵁ U))))) ≫
      (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalizationOpenCover.f ⟨U, hU⟩

/-- Pulling the actual global normalization back to the target stalk gives the literal
integral closure in the same original chart algebra. -/
theorem localNormalization_isPullback :
    IsPullback (localToNormalization X C U hU y)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
        (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
            (genericPoint X)) ⁻¹ᵁ U))))))
      (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
      (X.fromSpecStalk y) := by
  let := hU.isLocalization_stalk y
  let := originalAlgebra_atPrime_isLocalization X C U hU y
  have h := (localClosure_isPullback Γ(X, U) (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫
      X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))
    (hU.primeIdealOf y).asIdeal.primeCompl).paste_horiz (isPullback_chart X C U hU)
  have hg : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (X.presheaf.stalk y))) ≫
      hU.fromSpec = X.fromSpecStalk y :=
    hU.fromSpecStalk_eq_fromSpecStalk y.2
  rw [hg] at h
  exact h

/-- The proved cartesian square constructs the literal stalk-pullback comparison isomorphism. -/
def localFiberIso :
    Spec (.of (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
        (genericPoint X)) ⁻¹ᵁ U)))) ≅
      pullback (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk y) :=
  (localNormalization_isPullback X C U hU y).isoPullback

include hU in
/-- Etaleness of the literal local closure transfers along the constructed isomorphism
into the target-stalk pullback of the original cover's actual relative normalization. -/
theorem localPullback_etale_of_closure_etale
    (he : Algebra.Etale (X.presheaf.stalk y)
      (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
          (genericPoint X)) ⁻¹ᵁ U)))) :
    Etale (pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
      (X.fromSpecStalk y)) := by
  let := he
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
      (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
          (genericPoint X)) ⁻¹ᵁ U)))))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have : Etale ((localNormalization_isPullback X C U hU y).isoPullback.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
        (integralClosure (X.presheaf.stalk y) (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk
            (genericPoint X)) ⁻¹ᵁ U)))))) := inferInstance
  simpa only [IsPullback.isoPullback_inv_snd] using this

end ActualStalk

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.LocalComparison
