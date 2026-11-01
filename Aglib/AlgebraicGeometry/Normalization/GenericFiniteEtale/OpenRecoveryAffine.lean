/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.Affine
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericPullback
public import Aglib.AlgebraicGeometry.Spec.Localization

/-! # The original principal-open condition on an affine normalization

An actual generic-source comparison transports open recovery to the literal
integral closure. Only localization at the given principal open is used;
no normalization comparison for ramified base change is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
  (x : R)
  [Nonempty (Spec (.of (Localization.Away x)))]
  [∀ z : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk z)]

local instance : IsIntegral (Spec (.of (Localization.Away x))) :=
  isIntegral_of_isOpenImmersion (Spec.algebraMap R (Localization.Away x))

local instance affineRecoveryFieldAlgebra : Algebra R (Spec (.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)

/-- A comparison with the original generic cover supplies etaleness on the
literal principal-open localization of the same integral closure. The source
comparison and its structural equation are inputs to this reusable transport;
applications construct them from the original generic pullback. -/
theorem integralClosure_away_etale
    {E : Scheme.{u}} (p : E ⟶ Spec (.of (Localization.Away x)))
    [IsFinite p] [Etale p]
    (e : Spec (.of A) ≅
      (genericCover (Spec.algebraMap R (Localization.Away x)) p).obj.left)
    (he : e.hom ≫ genericMap (Spec.algebraMap R (Localization.Away x)) p =
      Spec.algebraMap R A) :
    Algebra.Etale R (Localization.Away (algebraMap R (integralClosure R A) x)) := by
  let j := Spec.algebraMap R (Localization.Away x)
  let g := genericMap j p
  let B := integralClosure R A
  let b := Spec.algebraMap R B
  let n : Spec (.of B) ≅ g.normalization :=
    Hom.specIntegralClosureNormalizationIso R A ≪≫
      Hom.normalizationSourceIso e (Spec.algebraMap R A) g he
  have hn : n.hom ≫ g.fromNormalization = b := by
    simp only [n, Iso.trans_hom, Category.assoc,
      Hom.normalizationSourceIso_hom_over,
      Hom.specIntegralClosureNormalizationIso_hom_over]
    rfl
  have hp : Etale (pullback.snd g.fromNormalization j) := by
    have h : pullback.snd g.fromNormalization j = (iso j p).inv ≫ p := by
      calc
        _ = (iso j p).inv ≫ ((iso j p).hom ≫ pullback.snd g.fromNormalization j) :=
          (Iso.inv_hom_id_assoc _ _).symm
        _ = (iso j p).inv ≫ p := congrArg ((iso j p).inv ≫ ·) (iso_hom_snd j p)
    rw [h]
    infer_instance
  let q := Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (Localization.Away x)
      (Localization.Away (algebraMap R B x)) (algebraMap R B) x))
  let i := Spec.algebraMap B (Localization.Away (algebraMap R B x))
  have H : IsPullback i q b j :=
    (Scheme.isPullback_specMap_localizationAway
      (CommRingCat.ofHom (algebraMap R B)) x).flip
  have H' : IsPullback (i ≫ n.hom) q g.fromNormalization j :=
    H.of_iso (Iso.refl _) n (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simpa using hn.symm) (by simp)
  have hq : Etale q := by
    rw [← H'.isoPullback_hom_snd]
    infer_instance
  have hcomp : Etale (i ≫ b) := by
    rw [H.w]
    infer_instance
  have hi : i ≫ b =
      Spec.algebraMap R (Localization.Away (algebraMap R B x)) := by
    simp only [i, b, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  rw [hi] at hcomp
  exact RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hcomp)

/-- For the actual base change of an integral finite-etale cover, the generic
comparison is constructed from the original function fields and generic maps.
The localized integral closure is therefore etale without a supplied generic
comparison or a normalization/base-change compatibility premise. -/
theorem baseChange_integralClosure_away_etale
    {X : Scheme.{u}} [IsIntegral X]
    (g : Spec (.of (Localization.Away x)) ⟶ X) [IsDominant g]
    (Y : Scheme.FiniteEtale X) [IsIntegral Y.obj.left] :
    letI := baseChangeFieldAlgebra (Spec.algebraMap R (Localization.Away x)) g
    letI := Scheme.FiniteEtale.GenericGalois.algebra Y
    Algebra.Etale R (Localization.Away
      (algebraMap R (integralClosure R
        ((Spec (.of R)).functionField ⊗[X.functionField] Y.obj.left.functionField)) x)) := by
  let := baseChangeFieldAlgebra (Spec.algebraMap R (Localization.Away x)) g
  let := Scheme.FiniteEtale.GenericGalois.algebra Y
  let p := ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom
  apply integralClosure_away_etale R _ x p
    (baseChangeFieldSpectrumIso (Spec.algebraMap R (Localization.Away x)) g Y)
  rw [baseChangeFieldSpectrumIso_hom_genericMap, Spec.fromSpecStalk_eq']
  change Spec.algebraMap (Spec (.of R)).functionField
      ((Spec (.of R)).functionField ⊗[X.functionField] Y.obj.left.functionField) ≫
    Spec.algebraMap R (Spec (.of R)).functionField = _
  simp only [Spec.algebraMap, ← Spec.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
