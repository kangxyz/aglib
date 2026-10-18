/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Principal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Congruence

/-!
# The same principal source on literal quotient ring heads

The original quotient-localization equivalence identifies the principal
source with the spectrum of its original composite ring homomorphism.
The same original restriction-congruence presents the released class map
on that literal source, preserving its native class-one value.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (r : A)

/-- The original principal source homomorphism, followed by the original quotient normalization. -/
def regularListPrincipalLiteralQuotientMap : regularListQuotientRing s ⟶
    regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r) :=
  CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))) ≫
    (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv

/-- Its spectrum is the same original composite principal source. -/
theorem regularListPrincipalLiteralQuotientMap_spec :
    Spec.map (regularListPrincipalLiteralQuotientMap s r) = regularListPrincipalSource s r := by
  rw [regularListPrincipalLiteralQuotientMap, Spec.map_comp]
  rfl

instance regularListPrincipalLiteralQuotientMap_isOpenImmersion :
    IsOpenImmersion (Spec.map (regularListPrincipalLiteralQuotientMap s r)) := by
  rw [regularListPrincipalLiteralQuotientMap_spec]
  infer_instance

/-- The literal source retains the original quotient square over the original
ambient localization. -/
theorem regularListPrincipalLiteralQuotientMap_square :
    (CommRingCat.ofHom (algebraMap A (Localization.Away r)) :
      A ⟶ CommRingCat.of (Localization.Away r)) ≫
        regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
          (regularListPrincipalList s r) =
      regularListQuotientMap s ≫ regularListPrincipalLiteralQuotientMap s r := by
  ext a
  apply (regularListPrincipalQuotientEquiv s r).injective
  change regularListPrincipalQuotientEquiv s r
      (Ideal.Quotient.mk (Ideal.ofList (regularListPrincipalList s r))
        (algebraMap A (Localization.Away r) a)) =
    regularListPrincipalQuotientEquiv s r
      ((regularListPrincipalQuotientEquiv s r).symm
        (algebraMap (A ⧸ Ideal.ofList s)
          (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
            (Ideal.Quotient.mk (Ideal.ofList s) a)))
  rw [regularListPrincipalQuotientEquiv_mk, RingEquiv.apply_symm_apply]
  simp only [IsLocalization.Away.map, IsLocalization.map_eq]

variable {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The same two-stage original principal map on its identical literal source spectrum. -/
def regularListPrincipalLiteralSheafHomologyMap (n : ℤ) :
    let φ : A ⟶ CommRingCat.of (Localization.Away r) :=
      CommRingCat.ofHom (algebraMap A (Localization.Away r))
    ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology n).restrict
        (Spec.map (regularListPrincipalLiteralQuotientMap s r)) ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex
        (R := CommRingCat.of (Localization.Away r)) (regularListPrincipalList s r)
          (affineOpenRestrictedInjectiveResolution φ J)).homology n := by
  intro φ
  exact (restrictFunctorCongr (regularListPrincipalLiteralQuotientMap_spec s r)).hom.app
      ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology n) ≫
    regularListPrincipalSingleRestrictionHomologyMap s r J n

variable (hs : RingTheory.Sequence.IsWeaklyRegular A s) [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

local instance : ((restrictFunctor (Spec.map
    (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).symm.app L)
    (isQuasicoherent_pullback (CommRingCat.ofHom (algebraMap A (Localization.Away r))) L)

/-- The identical literal principal source preserves the same original common-degree class one. -/
theorem regularListPrincipalLiteralSheafHomologyMap_modelTopClass
    (V : (Spec (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))).Opens) :
    let S := Localization.Away r
    let φ : A ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap A S)
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListPrincipalCoefficientFrame r e θ
    letI : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    (regularListPrincipalLiteralSheafHomologyMap s r J (s.length : ℤ)).val.app (op V)
      (regularListModelTopClass s hs J e (1 : A)
        ((Spec.map (regularListPrincipalLiteralQuotientMap s r)) ''ᵁ V)) =
      regularListModelTopClassInDegree (A := CommRingCat.of S)
        (regularListPrincipalList s r) (hs.of_flat (S := S)) J' e'
          s.length (List.length_map (as := s) (algebraMap A S)) (1 : S) V := by
  intro S φ J' θ e'
  let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
  change (regularListPrincipalSingleRestrictionHomologyMap s r J (s.length : ℤ)).val.app
    (op V) (((restrictFunctorCongr (regularListPrincipalLiteralQuotientMap_spec s r)).hom.app
      ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ))).val.app (op V)
      (regularListModelTopClass s hs J e (1 : A)
        ((Spec.map (regularListPrincipalLiteralQuotientMap s r)) ''ᵁ V))) = _
  rw [regularListModelTopClass_restrictFunctorCongr]
  exact regularListPrincipalSingleRestrictionHomologyMap_modelTopClass s r J hs e V

end AlgebraicGeometry.Scheme.Modules
