/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Homogeneity
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.SourcePullback
public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback

/-!
# Original multiplication pullback on the same Picard component

Universal Poincare homogeneity gives the actual family power law. Through
the same fppf representation it identifies pullback by native multiplication
on the original source with native multiplication on its original Picard
component, for every natural number, including zero and one.

The properness and geometric integrality of that component remain genuine
explicit hypotheses. The separate coherent H1 supplier is not assumed proved.
All identity, contravariant composition and field-base-change operations are
the original maps of `Picard.Scheme.Pullback`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local Scheme.Group

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsProper (picardIdentityComponent A.hom P R).hom]
  [GeometricallyIntegral (picardIdentityComponent A.hom P R).hom]

set_option backward.isDefEq.respectTransparency false in
/-- The original Poincare class is additive in its source coordinate on
every test scheme, with its parameter coordinate unchanged. -/
theorem poincareClass_pullback_mul {T : Over (Spec (.of k))} (f g : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) :
    pullbackClass (lift (f * g) d).left (poincareClass A P R) =
      pullbackClass (lift f d).left (poincareClass A P R) +
        pullbackClass (lift g d).left (poincareClass A P R) := by
  have h := congrArg (pullbackClass (lift f (𝟙 T)).left)
    (poincareTranslationClass_eq_basePullback A P R g d)
  have h₁ : lift f (𝟙 T) ≫ universalTranslationMorphism A g d = lift (f * g) d := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [universalTranslationMorphism, translationFamilyMorphism, MonObj.comp_mul]
  have h₂ : lift f (𝟙 T) ≫ translationFamilyMap A d = lift f d := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [translationFamilyMap]
  have h₁' : (lift f (𝟙 T)).left ≫ (universalTranslationMorphism A g d).left =
      (lift (f * g) d).left :=
    congrArg (fun q : T ⟶ A ⊗ picardIdentityComponent A.hom P R => q.left) h₁
  have h₂' : (lift f (𝟙 T)).left ≫ (translationFamilyMap A d).left =
      (lift f d).left :=
    congrArg (fun q : T ⟶ A ⊗ picardIdentityComponent A.hom P R => q.left) h₂
  simp only [universalTranslationClass] at h
  simp only [← pullbackHom_apply, map_sub] at h
  simp only [pullbackHom_apply, ← pullbackClass_comp] at h
  rw [h₁', h₂'] at h
  have hq : (lift f (𝟙 T)).left ≫ pullback.snd A.hom T.hom = 𝟙 T.left := by
    change (lift f (𝟙 T) ≫ snd A T).left = _
    rw [lift_snd, Over.id_left]
  rw [← Category.assoc, hq, Category.id_comp] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- All natural powers act by the corresponding multiple of the same
Poincare class, on arbitrary test schemes. -/
theorem poincareClass_pullback_pow {T : Over (Spec (.of k))} (f : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) (n : ℕ) :
    pullbackClass (lift (f ^ n) d).left (poincareClass A P R) =
      n • pullbackClass (lift f d).left (poincareClass A P R) := by
  induction n with
  | zero =>
      rw [pow_zero, zero_nsmul]
      have h : lift (1 : T ⟶ A) d =
          d ≫ lift (1 : picardIdentityComponent A.hom P R ⟶ A)
            (𝟙 (picardIdentityComponent A.hom P R)) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [h, Over.comp_left, pullbackClass_comp, poincareClass_source_unit,
        pullbackClass_zero]
  | succ n ih =>
      rw [pow_succ, poincareClass_pullback_mul, ih, add_nsmul, one_nsmul]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback by the literal source-family map of native multiplication
acts by n on the original universal Poincare class. -/
theorem poincareClass_multiplication_pullback (n : ℕ) :
    pullbackClass
        (familyMapOfHom ((𝟙 A) ^ n) (picardIdentityComponent A.hom P R))
        (poincareClass A P R) =
      n • poincareClass A P R := by
  let D := picardIdentityComponent A.hom P R
  have h : familyMapOfHom ((𝟙 A) ^ n) D =
      (lift ((fst A D) ^ n) (snd A D)).left := by
    rw [familyMapOfHom_eq_tensorHom A]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_pow]
  rw [h, poincareClass_pullback_pow, lift_fst_snd, Over.id_left]
  change n • pullbackClass (𝟙 (pullback A.hom D.hom)) (poincareClass A P R) = _
  rw [pullbackClass_id]

set_option backward.isDefEq.respectTransparency false in
/-- The original Picard pullback of native `[n]` is native `[n]` on the
same identity component, for every natural n. -/
theorem picardIdentityComponentPullback_multiplication (n : ℕ) :
    picardIdentityComponentPullback P R P R ((𝟙 A) ^ n) =
      (𝟙 (picardIdentityComponent A.hom P R)) ^ n := by
  let := picardCommGrpObj A.hom P R
  let D := picardIdentityComponent A.hom P R
  let i : D ⟶ P.obj := picardIdentityComponentι A.hom P R
  let : IsMonHom i := isMonHom_picardIdentityComponentι A.hom P R
  have : IsLocallyNoetherian D.left := LocallyOfFiniteType.isLocallyNoetherian D.hom
  let T : LocallyNoetherianOver (Spec (.of k)) := ⟨D, inferInstance⟩
  let a := poincareClass A P R
  let f : A ⟶ A := (𝟙 A) ^ n
  let u : D ⟶ D := picardIdentityComponentPullback P R P R f
  let q : PicardGroup (pullback A.hom D.hom) →+
      (fppfPicardSheaf A.hom).obj.obj (op D) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op D)).hom
  let E : Additive (D ⟶ P.obj) ≃+ (fppfPicardSheaf A.hom).obj.obj (op D) :=
    picardHomAddEquiv A.hom P R T
  have ha : q a = E (Additive.ofMul i) := by
    have hi := poincarePullback_fppfClass A P R (T := T) (𝟙 D)
    change q (classOf (pullback A.hom D.hom) (poincarePullback A P R (𝟙 D)).bundle) =
      E (Additive.ofMul (𝟙 D ≫ i)) at hi
    have he : classOf (pullback A.hom D.hom)
        (poincarePullback A P R (𝟙 D)).bundle = a :=
      Quotient.sound ⟨(poincarePullbackIdIso A P R).iso⟩
    rw [he, Category.id_comp] at hi
    exact hi
  change u = (𝟙 D) ^ n
  apply (cancel_mono i).mp
  suffices h : E (Additive.ofMul (u ≫ i)) =
      E (Additive.ofMul (((𝟙 D) ^ n) ≫ i)) from
    congrArg Additive.toMul (E.injective h)
  have hp' : ((𝟙 D) ^ n) ≫ i = i ^ n := by rw [MonObj.pow_comp, Category.id_comp]
  rw [hp', _root_.ofMul_pow, map_nsmul]
  have hdual := homEquiv_comp_picardIdentityComponentPullback P R P R f (T := T) (𝟙 D)
  change E (Additive.ofMul ((𝟙 D ≫ u) ≫ i)) =
    ((fppfPicardPullback f).hom.app (op D)).hom
      (E (Additive.ofMul (𝟙 D ≫ i))) at hdual
  simp only [Category.id_comp] at hdual
  have hsource := fppfPicardPullback_class f D a
  change q (pullbackClass (familyMapOfHom f D) a) =
    ((fppfPicardPullback f).hom.app (op D)).hom (q a) at hsource
  calc
    E (Additive.ofMul (u ≫ i)) =
        ((fppfPicardPullback f).hom.app (op D)).hom (E (Additive.ofMul i)) := hdual
    _ = ((fppfPicardPullback f).hom.app (op D)).hom (q a) := by rw [ha]
    _ = q (pullbackClass (familyMapOfHom f D) a) := hsource.symm
    _ = q (n • a) := congrArg q (poincareClass_multiplication_pullback A P R n)
    _ = n • q a := map_nsmul q n a
    _ = n • E (Additive.ofMul i) := by rw [ha]

/-- The zero multiplication endpoint is included in the same original law. -/
theorem picardIdentityComponentPullback_multiplication_zero :
    picardIdentityComponentPullback P R P R (1 : A ⟶ A) =
      (1 : picardIdentityComponent A.hom P R ⟶ picardIdentityComponent A.hom P R) := by
  simpa only [pow_zero] using picardIdentityComponentPullback_multiplication A P R 0

/-- Contravariant composition uses the same multiplication maps and the
already constructed original Picard pullback. -/
theorem picardIdentityComponentPullback_multiplication_comp (m n : ℕ) :
    picardIdentityComponentPullback P R P R (((𝟙 A) ^ m) ≫ ((𝟙 A) ^ n)) =
      ((𝟙 (picardIdentityComponent A.hom P R)) ^ n) ≫
        ((𝟙 (picardIdentityComponent A.hom P R)) ^ m) := by
  rw [picardIdentityComponentPullback_comp P R P R P R,
    picardIdentityComponentPullback_multiplication,
    picardIdentityComponentPullback_multiplication]

/-- The multiplication identification respects the original field-extension
square, using the same representatives and component comparison isomorphism. -/
theorem picardIdentityComponentPullback_multiplication_baseChange
    (K : Type u) [Field K] [Algebra k K] (n : ℕ) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    letI := picardCommGrpObj A.hom P R
    letI := picardCommGrpObj (pullback.snd A.hom b)
      (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy A.hom b P R)
    ((Over.pullback b).map ((𝟙 (picardIdentityComponent A.hom P R)) ^ n)).left ≫
        (picardIdentityComponentBaseChangeIso A.hom P R K).hom =
      (picardIdentityComponentBaseChangeIso A.hom P R K).hom ≫
        (picardIdentityComponentPullback
          (X := (Over.pullback b).obj A) (Y := (Over.pullback b).obj A)
          (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy A.hom b P R)
          (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy A.hom b P R)
          ((Over.pullback b).map ((𝟙 A) ^ n))).left := by
  simpa only [picardIdentityComponentPullback_multiplication] using
    (picardIdentityComponentPullback_baseChange P R P R K ((𝟙 A) ^ n))

end AlgebraicGeometry.Scheme.RelativePicard
