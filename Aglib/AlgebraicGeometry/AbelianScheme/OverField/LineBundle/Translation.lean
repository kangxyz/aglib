/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Cube
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Morphism
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.TranslationIso
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Rigidified

/-!
# Translation and inversion invariance of the original line-bundle morphism

The cube identity is first applied to arbitrary scheme-valued morphisms. Its
quadratic cross-effect is unchanged by rational translation of the original
bundle or by pullback under group inversion. The normalized family equations
and their actual parameter-pullback laws hold on all tests, including nonreduced
ones. Only then does the same supplied Picard representation give equality of
the original morphisms and of their actual identity-component factors.

Group inversion pullback is distinct from the dual of a line bundle. In Milne,
Jacobian Varieties (2021), Lemma 6.9, inversion of the theta divisor preserves
its line-bundle morphism; the separate parameter inversion accounts for the
minus sign in `-f^vee = phi_Theta^-1`. No autoduality or pairing sign is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.LineBundleCube

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

/-- Translation invariance of the original quadratic pullback expression
on every test scheme, with no reducedness or Noetherian hypothesis. -/
theorem pullbackClass_crossEffect_translation {S : Over (Spec (.of k))}
    (f g : S ⟶ G) (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (f * g).left (pullbackClass (GrpObj.mulRight b).hom.left a) -
        pullbackClass f.left (pullbackClass (GrpObj.mulRight b).hom.left a) -
        pullbackClass g.left (pullbackClass (GrpObj.mulRight b).hom.left a) =
      pullbackClass (f * g).left a - pullbackClass f.left a - pullbackClass g.left a := by
  have ht (v : S ⟶ G) : v ≫ (GrpObj.mulRight b).hom = v * (toUnit S ≫ b) := by
    change v ≫ ((𝟙 G) * (toUnit G ≫ b)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  simp only [← pullbackClass_comp, ← Over.comp_left, ht]
  apply sub_eq_zero.mp
  have hc := cubeClass_eq_zero G f g (toUnit S ≫ b) a
  simp only [cubeClass, pullbackHom_apply, pullbackClass_constant, add_zero] at hc
  convert hc using 1
  abel

/-- Inversion invariance of the same quadratic expression. Commutativity
is supplied by the original proper geometrically integral group theorem;
no statement about inversion on Picard identity components is used. -/
theorem pullbackClass_crossEffect_inv {S : Over (Spec (.of k))}
    (f g : S ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (f * g).left (pullbackClass ι[G].left a) -
        pullbackClass f.left (pullbackClass ι[G].left a) -
        pullbackClass g.left (pullbackClass ι[G].left a) =
      pullbackClass (f * g).left a - pullbackClass f.left a - pullbackClass g.left a := by
  let : IsCommMonObj G := isCommMonObj_of_isProper_of_geometricallyIntegral G
  let F : (S ⟶ G) → PicardGroup S.left := fun v => pullbackClass v.left a
  let B : (S ⟶ G) → (S ⟶ G) → PicardGroup S.left := fun v w => F (v * w) - F v - F w
  have hB (v w z : S ⟶ G) : B (v * w) z = B v z + B w z := by
    apply sub_eq_zero.mp
    have hc := cubeClass_eq_zero G v w z a
    simp only [cubeClass, pullbackHom_apply] at hc
    change (F (v * w * z) - F (v * w) - F z) -
      ((F (v * z) - F v - F z) + (F (w * z) - F w - F z)) = 0
    convert hc using 1
    dsimp only [F]
    abel
  have hs (v w : S ⟶ G) : B v w = B w v := by
    dsimp only [B]
    rw [_root_.mul_comm v w]
    abel
  have hzero (v : S ⟶ G) : B 1 v = 0 := by
    simp only [B, F, _root_.one_mul, pullbackClass_one, sub_zero, sub_self]
  have hinv (v w : S ⟶ G) : B v⁻¹ w = -B v w := by
    have h := hB v v⁻¹ w
    rw [_root_.mul_inv_cancel, hzero] at h
    apply eq_neg_iff_add_eq_zero.mpr
    rw [_root_.add_comm]
    exact h.symm
  have hboth : B f⁻¹ g⁻¹ = B f g := by
    rw [hinv, hs f g⁻¹, hinv, neg_neg, hs g f]
  simp only [← pullbackClass_comp, ← Over.comp_left]
  change F ((f * g)⁻¹) - F f⁻¹ - F g⁻¹ = B f g
  rw [_root_.mul_inv_rev, _root_.mul_comm g⁻¹ f⁻¹]
  exact hboth

end AlgebraicGeometry.Scheme.Group.LineBundleCube

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
open Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translating a fixed bundle by an ARBITRARY PARAMETER-valued point
preserves its normalized difference family. This is the whole cube identity
on the original product, including nonreduced and non-Noetherian tests. -/
theorem normalized_translationFamilyClass_mul_sub
    {T : Over (Spec (.of k))} (t b : T ⟶ G) (a : PicardGroup G.left) :
    normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G (t * b) a - translationFamilyClass G b a) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t a) := by
  rw [map_sub]
  apply Subtype.ext
  change ((normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
      (translationFamilyClass G (t * b) a)).val -
    (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
      (translationFamilyClass G b a)).val : PicardGroup (G ⊗ T).left) = _
  rw [normalized_translationFamilyClass_eq_translationFamily_pullback,
    normalized_translationFamilyClass_eq_translationFamily_pullback,
    normalized_translationFamilyClass_eq_translationFamily_pullback]
  simp only [← pullbackClass_comp, ← Over.comp_left,
    GrpObj.translationFamily_hom_fst, MonObj.comp_mul, ← _root_.mul_assoc]
  let F : ((G ⊗ T) ⟶ G) → PicardGroup (G ⊗ T).left := fun v => pullbackClass v.left a
  let u := fst G T
  let v := snd G T ≫ t
  let w := snd G T ≫ b
  change (F (u * v * w) - F u - F (v * w)) -
    (F (u * w) - F u - F w) = F (u * v) - F u - F v
  apply sub_eq_zero.mp
  have hc := LineBundleCube.cubeClass_eq_zero G u v w a
  change F (u * v * w) - F (u * v) - F (u * w) - F (v * w) + F u + F v + F w = 0 at hc
  calc
    _ = F (u * v * w) - F (u * v) - F (u * w) - F (v * w) + F u + F v + F w := by abel
    _ = 0 := hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The preceding arbitrary-parameter law on the ACTUAL translated
bundle family: translate the coefficient by b, then take its t-difference.
Both operations use the same native shear and original family morphism. -/
theorem normalized_translationFamilyClass_parameter_translation
    {T : Over (Spec (.of k))} (t b : T ⟶ G) (a : PicardGroup G.left) :
    normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (pullbackClass (GrpObj.translationFamily G t).hom.left
            (pullbackClass (translationFamilyMorphism G b).left a) -
          pullbackClass (translationFamilyMorphism G b).left a) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t a) := by
  have hm : (GrpObj.translationFamily G t).hom ≫ translationFamilyMorphism G b =
      translationFamilyMorphism G (t * b) := by
    rw [translationFamilyMorphism_eq_translationFamily_hom_fst,
      translationFamilyMorphism_eq_translationFamily_hom_fst, GrpObj.translationFamily_mul]
    simp only [Iso.trans_hom, Category.assoc]
  have hclass : pullbackClass (GrpObj.translationFamily G t).hom.left
        (pullbackClass (translationFamilyMorphism G b).left a) -
      pullbackClass (translationFamilyMorphism G b).left a =
      translationFamilyClass G (t * b) a - translationFamilyClass G b a := by
    rw [← pullbackClass_comp, ← Over.comp_left, hm]
    simp only [translationFamilyClass]
    abel
  rw [hclass]
  exact normalized_translationFamilyClass_mul_sub G t b a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The arbitrary-parameter difference comparison is natural in the
original test-scheme map. Both parameter points are pulled back. -/
theorem normalized_translationFamilyClass_parameter_naturality
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t b : T ⟶ G) (a : PicardGroup G.left) :
    ((normalizedPicardFunctor G.hom η[G].left (Over.w η[G])).map f.op).hom
        (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
          (translationFamilyClass G (t * b) a - translationFamilyClass G b a)) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T'
        (translationFamilyClass G (f ≫ t) a) := by
  rw [normalized_translationFamilyClass_mul_sub, ← normalizedFamilyClass_pullback,
    translationFamilyClass_pullback]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original normalized translated family is unchanged by translation
of the original class. Its first coordinate is the canonical native shear. -/
theorem normalized_translationFamilyClass_pullback_translation
    {T : Over (Spec (.of k))} (t : T ⟶ G)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (a : PicardGroup G.left) :
    normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t (pullbackClass (GrpObj.mulRight b).hom.left a)) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t a) := by
  apply Subtype.ext
  rw [normalized_translationFamilyClass_eq_translationFamily_pullback,
    normalized_translationFamilyClass_eq_translationFamily_pullback]
  simp only [← pullbackClass_comp, ← Over.comp_left,
    GrpObj.translationFamily_hom_fst, GrpObj.translationFamily_hom_fst_assoc]
  simpa only [← pullbackClass_comp, ← Over.comp_left, Category.assoc] using
    LineBundleCube.pullbackClass_crossEffect_translation G (fst G T) (snd G T ≫ t) b a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original normalized family is also unchanged by inversion pullback
of the bundle, on arbitrary test schemes including nilpotent ones. -/
theorem normalized_translationFamilyClass_pullback_inv
    {T : Over (Spec (.of k))} (t : T ⟶ G) (a : PicardGroup G.left) :
    normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t (pullbackClass ι[G].left a)) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t a) := by
  apply Subtype.ext
  rw [normalized_translationFamilyClass_eq_translationFamily_pullback,
    normalized_translationFamilyClass_eq_translationFamily_pullback]
  simp only [← pullbackClass_comp, ← Over.comp_left,
    GrpObj.translationFamily_hom_fst, GrpObj.translationFamily_hom_fst_assoc]
  simpa only [← pullbackClass_comp, ← Over.comp_left, Category.assoc] using
    LineBundleCube.pullbackClass_crossEffect_inv G (fst G T) (snd G T ≫ t) a

set_option backward.isDefEq.respectTransparency false in
/-- The translation comparison commutes with the original normalized
Picard pullback for every parameter morphism, without Noetherian restrictions. -/
theorem normalized_translationFamilyClass_translation_naturality
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (a : PicardGroup G.left) :
    ((normalizedPicardFunctor G.hom η[G].left (Over.w η[G])).map f.op).hom
        (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
          (translationFamilyClass G t (pullbackClass (GrpObj.mulRight b).hom.left a))) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T'
        (translationFamilyClass G (f ≫ t) a) := by
  rw [← normalizedFamilyClass_pullback, translationFamilyClass_pullback]
  exact normalized_translationFamilyClass_pullback_translation G (f ≫ t) b a

set_option backward.isDefEq.respectTransparency false in
/-- Inversion comparison commutes with the same original parameter-pullback
maps, on all tests including nonreduced schemes. -/
theorem normalized_translationFamilyClass_inv_naturality
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G) (a : PicardGroup G.left) :
    ((normalizedPicardFunctor G.hom η[G].left (Over.w η[G])).map f.op).hom
        (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
          (translationFamilyClass G t (pullbackClass ι[G].left a))) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T'
        (translationFamilyClass G (f ≫ t) a) := by
  rw [← normalizedFamilyClass_pullback, translationFamilyClass_pullback]
  exact normalized_translationFamilyClass_pullback_inv G (f ≫ t) a

omit [IsHProjective G.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem existsUnique_normalizedFamilyIso_of_class_eq
    [IsProper G.hom]
    {T : Over (Spec (.of k))} (L M : LineBundle (pullback G.hom T.hom))
    (h : normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T (classOf _ L) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T (classOf _ M)) :
    ∃! _e : RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T L)
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T M), True := by
  have hc : classOf _ (normalizedFamilyLineBundle G.hom η[G].left (Over.w η[G]) T L) =
      classOf _ (normalizedFamilyLineBundle G.hom η[G].left (Over.w η[G]) T M) := by
    rw [classOf_normalizedFamilyLineBundle, classOf_normalizedFamilyLineBundle]
    exact congrArg Subtype.val h
  obtain ⟨e⟩ := (class_eq_iff _ _ _).mp hc
  let q := RigidifiedPair.isoOfBundleIso
    (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T L)
    (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T M) e
  refine ⟨q, trivial, ?_⟩
  intro q' _
  exact RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) q' q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The arbitrary-parameter translation equation is a UNIQUE isomorphism
of the original normalized rigidified bundles, including nilpotent tests. -/
theorem existsUnique_normalizedTranslationFamilyParameterIso
    {T : Over (Spec (.of k))} (t b : T ⟶ G) (L : LineBundle G.left) :
    let M := pullbackLineBundle (translationFamilyMorphism G b).left L
    let D := tensorLineBundle (pullback G.hom T.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t).hom.left M)
      (dualLineBundle _ M)
    ∃! _e : RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T D)
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)), True := by
  dsimp only
  apply existsUnique_normalizedFamilyIso_of_class_eq G
  rw [classOf_tensor, classOf_dual, classOf_translationFamilyLineBundle]
  simp only [← pullbackClass_classOf, ← sub_eq_add_neg]
  exact normalized_translationFamilyClass_parameter_translation G t b (classOf _ L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translation gives a UNIQUE isomorphism of the actual normalized
rigidified families, on every test scheme. This retains the selected bundles
and rigidifications, rather than only their values at geometric points. -/
theorem existsUnique_normalizedTranslationFamilyTranslationIso
    {T : Over (Spec (.of k))} (t : T ⟶ G)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (L : LineBundle G.left) :
    ∃! _e : RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t (pullbackLineBundle (GrpObj.mulRight b).hom.left L)))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)), True := by
  apply existsUnique_normalizedFamilyIso_of_class_eq G
  rw [classOf_translationFamilyLineBundle, classOf_translationFamilyLineBundle,
    ← pullbackClass_classOf]
  exact normalized_translationFamilyClass_pullback_translation G t b (classOf _ L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inversion pullback gives the same unique actual rigidified-family
isomorphism boundary. Inverse and naturality diagrams between these fixed
families are controlled by the original rigidified-pair uniqueness theorem. -/
theorem existsUnique_normalizedTranslationFamilyInvIso
    {T : Over (Spec (.of k))} (t : T ⟶ G) (L : LineBundle G.left) :
    ∃! _e : RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t (pullbackLineBundle ι[G].left L)))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)), True := by
  apply existsUnique_normalizedFamilyIso_of_class_eq G
  rw [classOf_translationFamilyLineBundle, classOf_translationFamilyLineBundle,
    ← pullbackClass_classOf]
  exact normalized_translationFamilyClass_pullback_inv G t (classOf _ L)

/-- The unique rigidified comparison for translation of the coefficient. -/
def normalizedTranslationFamilyTranslationIso
    {T : Over (Spec (.of k))} (t : T ⟶ G)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (L : LineBundle G.left) :
    RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t (pullbackLineBundle (GrpObj.mulRight b).hom.left L)))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)) :=
  Classical.choose (existsUnique_normalizedTranslationFamilyTranslationIso G t b L).exists

/-- The unique rigidified comparison for inversion pullback of the coefficient. -/
def normalizedTranslationFamilyInvIso
    {T : Over (Spec (.of k))} (t : T ⟶ G) (L : LineBundle G.left) :
    RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t (pullbackLineBundle ι[G].left L)))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)) :=
  Classical.choose (existsUnique_normalizedTranslationFamilyInvIso G t L).exists

/-- The unique comparison for a parameter-valued translated coefficient. -/
def normalizedTranslationFamilyParameterIso
    {T : Over (Spec (.of k))} (t b : T ⟶ G) (L : LineBundle G.left) :
    let M := pullbackLineBundle (translationFamilyMorphism G b).left L
    let D := tensorLineBundle (pullback G.hom T.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t).hom.left M)
      (dualLineBundle _ M)
    RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T D)
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)) :=
  Classical.choose (existsUnique_normalizedTranslationFamilyParameterIso G t b L).exists

omit [IsHProjective G.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of the original normalized translated pair agrees with the
pair at the pulled-back parameter. Both the module pullback and its
rigidification are the existing ones. -/
theorem existsUnique_normalizedTranslationFamilyPullbackIso
    [IsProper G.hom]
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G) (L : LineBundle G.left) :
    ∃! _e : RigidifiedPair.Iso
      (RigidifiedPair.map f (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T'
        (translationFamilyLineBundle G (f ≫ t) L)), True := by
  let q : pullback G.hom T'.hom ⟶ pullback G.hom T.hom := (familyScheme G.hom).map f
  have h := existsUnique_normalizedFamilyIso_of_class_eq G
    (pullbackLineBundle q (translationFamilyLineBundle G t L))
    (translationFamilyLineBundle G (f ≫ t) L) (by
      rw [← pullbackClass_classOf, classOf_translationFamilyLineBundle,
        classOf_translationFamilyLineBundle]
      exact congrArg (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T')
        (translationFamilyClass_pullback G f t (classOf _ L)))
  let e := (normalizedFamilyRigidifiedPairMapIso G.hom η[G].left (Over.w η[G]) f
    (translationFamilyLineBundle G t L)).trans (Classical.choose h.exists)
  refine ⟨e, trivial, ?_⟩
  intro e' _
  exact RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) e' e

omit [IsHProjective G.hom] in
/-- The unique actual rigidified comparison for the pulled-back parameter. -/
def normalizedTranslationFamilyPullbackIso
    [IsProper G.hom]
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G) (L : LineBundle G.left) :
    RigidifiedPair.Iso
      (RigidifiedPair.map f (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L)))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T'
        (translationFamilyLineBundle G (f ≫ t) L)) :=
  Classical.choose (existsUnique_normalizedTranslationFamilyPullbackIso G f t L).exists

omit [IsHProjective G.hom] [GeometricallyIntegral G.hom] in
/-- Equality of the original parameter gives the literal comparison of
the same normalized translated pairs. -/
def normalizedTranslationFamilyCongrIso
    {T : Over (Spec (.of k))} {t t' : T ⟶ G} (h : t = t') (L : LineBundle G.left) :
    RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t L))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
        (translationFamilyLineBundle G t' L)) :=
  h ▸ RigidifiedPair.Iso.refl _

omit [IsHProjective G.hom] in
/-- The original family-pullback comparison has the identity coherence law. -/
theorem normalizedTranslationFamilyPullbackIso_id
    [IsProper G.hom]
    {T : Over (Spec (.of k))} (t : T ⟶ G) (L : LineBundle G.left) :
    (normalizedTranslationFamilyPullbackIso G (𝟙 T) t L).trans
        (normalizedTranslationFamilyCongrIso G (Category.id_comp t) L) =
      RigidifiedPair.mapIdIso
        (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T
          (translationFamilyLineBundle G t L)) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

omit [IsHProjective G.hom] in
/-- Composition coherence uses the native rigidified pullback comparison,
before any evaluation on points or represented tests. -/
theorem normalizedTranslationFamilyPullbackIso_comp
    [IsProper G.hom]
    {T₀ T₁ T₂ : Over (Spec (.of k))} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂)
    (t : T₂ ⟶ G) (L : LineBundle G.left) :
    (normalizedTranslationFamilyPullbackIso G (f ≫ g) t L).trans
        (normalizedTranslationFamilyCongrIso G (Category.assoc f g t) L) =
      (RigidifiedPair.mapCompIso f g
        (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T₂
          (translationFamilyLineBundle G t L))).trans
        ((RigidifiedPair.Iso.map f (normalizedTranslationFamilyPullbackIso G g t L)).trans
          (normalizedTranslationFamilyPullbackIso G f (g ≫ t) L)) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

/-- Translation invariance commutes with the original actual pullback
comparisons on every parameter scheme. -/
theorem normalizedTranslationFamilyTranslationIso_naturality
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (L : LineBundle G.left) :
    (RigidifiedPair.Iso.map f (normalizedTranslationFamilyTranslationIso G t b L)).trans
        (normalizedTranslationFamilyPullbackIso G f t L) =
      (normalizedTranslationFamilyPullbackIso G f t
        (pullbackLineBundle (GrpObj.mulRight b).hom.left L)).trans
          (normalizedTranslationFamilyTranslationIso G (f ≫ t) b L) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

/-- Inversion invariance has the same whole rigidified naturality square. -/
theorem normalizedTranslationFamilyInvIso_naturality
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G) (L : LineBundle G.left) :
    (RigidifiedPair.Iso.map f (normalizedTranslationFamilyInvIso G t L)).trans
        (normalizedTranslationFamilyPullbackIso G f t L) =
      (normalizedTranslationFamilyPullbackIso G f t (pullbackLineBundle ι[G].left L)).trans
        (normalizedTranslationFamilyInvIso G (f ≫ t) L) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

/-- Actual pullback of the normalized difference of a parameter-translated
coefficient. The comparison is unique; its construction uses the original
pullback of rigidified pairs and pulls back BOTH parameters. -/
def normalizedTranslationFamilyParameterPullbackIso
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t b : T ⟶ G) (L : LineBundle G.left) :
    let M := pullbackLineBundle (translationFamilyMorphism G b).left L
    let D := tensorLineBundle (pullback G.hom T.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t).hom.left M) (dualLineBundle _ M)
    let M' := pullbackLineBundle (translationFamilyMorphism G (f ≫ b)).left L
    let D' := tensorLineBundle (pullback G.hom T'.hom)
      (pullbackLineBundle (GrpObj.translationFamily G (f ≫ t)).hom.left M') (dualLineBundle _ M')
    RigidifiedPair.Iso
      (RigidifiedPair.map f (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T D))
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T' D') :=
  (RigidifiedPair.Iso.map f (normalizedTranslationFamilyParameterIso G t b L)).trans
    ((normalizedTranslationFamilyPullbackIso G f t L).trans
      (normalizedTranslationFamilyParameterIso G (f ≫ t) (f ≫ b) L).symm)

/-- The arbitrary-parameter comparison commutes with the actual rigidified
family pullback. This statement holds on all schemes, without representability. -/
theorem normalizedTranslationFamilyParameterIso_naturality
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t b : T ⟶ G) (L : LineBundle G.left) :
    (RigidifiedPair.Iso.map f (normalizedTranslationFamilyParameterIso G t b L)).trans
        (normalizedTranslationFamilyPullbackIso G f t L) =
      (normalizedTranslationFamilyParameterPullbackIso G f t b L).trans
        (normalizedTranslationFamilyParameterIso G (f ≫ t) (f ≫ b) L) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

omit [IsHProjective G.hom] [GeometricallyIntegral G.hom] in
/-- Equality of both original parameters gives the literal comparison of
their existing normalized difference bundles. -/
def normalizedTranslationFamilyParameterCongrIso
    {T : Over (Spec (.of k))} {t t' b b' : T ⟶ G}
    (ht : t = t') (hb : b = b') (L : LineBundle G.left) :
    let M := pullbackLineBundle (translationFamilyMorphism G b).left L
    let D := tensorLineBundle (pullback G.hom T.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t).hom.left M) (dualLineBundle _ M)
    let M' := pullbackLineBundle (translationFamilyMorphism G b').left L
    let D' := tensorLineBundle (pullback G.hom T.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t').hom.left M') (dualLineBundle _ M')
    RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T D)
      (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T D') := by
  cases ht
  cases hb
  exact RigidifiedPair.Iso.refl _

/-- Identity coherence for the same parameter-translated coefficient family. -/
theorem normalizedTranslationFamilyParameterPullbackIso_id
    {T : Over (Spec (.of k))} (t b : T ⟶ G) (L : LineBundle G.left) :
    let M := pullbackLineBundle (translationFamilyMorphism G b).left L
    let D := tensorLineBundle (pullback G.hom T.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t).hom.left M) (dualLineBundle _ M)
    (normalizedTranslationFamilyParameterPullbackIso G (𝟙 T) t b L).trans
        (normalizedTranslationFamilyParameterCongrIso G
          (Category.id_comp t) (Category.id_comp b) L) =
      RigidifiedPair.mapIdIso
        (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T D) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

/-- Composition coherence for arbitrary parameter-valued translations,
including nonreduced double and triple bases. -/
theorem normalizedTranslationFamilyParameterPullbackIso_comp
    {T₀ T₁ T₂ : Over (Spec (.of k))} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂)
    (t b : T₂ ⟶ G) (L : LineBundle G.left) :
    let M := pullbackLineBundle (translationFamilyMorphism G b).left L
    let D := tensorLineBundle (pullback G.hom T₂.hom)
      (pullbackLineBundle (GrpObj.translationFamily G t).hom.left M) (dualLineBundle _ M)
    (normalizedTranslationFamilyParameterPullbackIso G (f ≫ g) t b L).trans
        (normalizedTranslationFamilyParameterCongrIso G
          (Category.assoc f g t) (Category.assoc f g b) L) =
      (RigidifiedPair.mapCompIso f g
        (normalizedFamilyRigidifiedPair G.hom η[G].left (Over.w η[G]) T₂ D)).trans
          ((RigidifiedPair.Iso.map f
            (normalizedTranslationFamilyParameterPullbackIso G g t b L)).trans
              (normalizedTranslationFamilyParameterPullbackIso G f (g ≫ t) (g ≫ b) L)) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (Over.w η[G]) _ _

/-- The two inverse laws for the actual inversion-invariance comparison. -/
theorem normalizedTranslationFamilyInvIso_inverse
    {T : Over (Spec (.of k))} (t : T ⟶ G) (L : LineBundle G.left) :
    let e := normalizedTranslationFamilyInvIso G t L
    e.trans e.symm = RigidifiedPair.Iso.refl _ ∧
      e.symm.trans e = RigidifiedPair.Iso.refl _ :=
  ⟨RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
      G.hom η[G].left (Over.w η[G]) _ _,
    RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
      G.hom η[G].left (Over.w η[G]) _ _⟩

/-- The two inverse laws also hold for arbitrary parameter-valued translation. -/
theorem normalizedTranslationFamilyParameterIso_inverse
    {T : Over (Spec (.of k))} (t b : T ⟶ G) (L : LineBundle G.left) :
    let e := normalizedTranslationFamilyParameterIso G t b L
    e.trans e.symm = RigidifiedPair.Iso.refl _ ∧
      e.symm.trans e = RigidifiedPair.Iso.refl _ :=
  ⟨RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
      G.hom η[G].left (Over.w η[G]) _ _,
    RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
      G.hom η[G].left (Over.w η[G]) _ _⟩

variable (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole classifying morphism for translating the original bundle by
a parameter-valued point b over a locally Noetherian T. Its domain is the
ACTUAL G x T, and the same supplied normalized representation is used. -/
def lineBundleClassMorphismTranslatedFamily
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    G ⊗ T.obj ⟶ P.obj :=
  let U : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G ⊗ T.obj, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd G.hom T.obj.hom)⟩
  (normalizedFamilyClassifyingMap G.hom η[G].left (Over.w η[G])
    (lineBundleNormalizedRepresentation G P R) U
      (translationFamilyClass G (fst G T.obj * (snd G T.obj ≫ b)) a -
        translationFamilyClass G (snd G T.obj ≫ b) a)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole arbitrary-parameter translated-family map equals the original
phi followed after the original projection. The representation is used only
on locally Noetherian tests; T is allowed to be nonreduced. -/
theorem lineBundleClassMorphismTranslatedFamily_eq
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    lineBundleClassMorphismTranslatedFamily G P R T b a =
      fst G T.obj ≫ lineBundleClassMorphism G P R a := by
  let U : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G ⊗ T.obj, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd G.hom T.obj.hom)⟩
  have h : (ObjectProperty.homMk (lineBundleClassMorphismTranslatedFamily G P R T b a) : U ⟶ P) =
      ObjectProperty.homMk (fst G T.obj ≫ lineBundleClassMorphism G P R a) := by
    apply (lineBundleNormalizedRepresentation G P R).homEquiv.injective
    change (lineBundleNormalizedRepresentation G P R).homEquiv
        (normalizedFamilyClassifyingMap G.hom η[G].left (Over.w η[G])
          (lineBundleNormalizedRepresentation G P R) U
          (translationFamilyClass G (fst G T.obj * (snd G T.obj ≫ b)) a -
            translationFamilyClass G (snd G T.obj ≫ b) a)) = _
    rw [homEquiv_normalizedFamilyClassifyingMap, homEquiv_comp_lineBundleClassMorphism]
    exact normalized_translationFamilyClass_mul_sub G (fst G T.obj) (snd G T.obj ≫ b) a
  exact congrArg (fun f : U ⟶ P => f.hom) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the WHOLE original classifying map for parameter-valued
translation, before evaluating on further test points. -/
theorem lineBundleClassMorphismTranslatedFamily_naturality
    {T T' : LocallyNoetherianOver (Spec (.of k))} (f : T' ⟶ T)
    (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    translationFamilyMap G f.hom ≫ lineBundleClassMorphismTranslatedFamily G P R T b a =
      lineBundleClassMorphismTranslatedFamily G P R T' (f.hom ≫ b) a := by
  rw [lineBundleClassMorphismTranslatedFamily_eq, lineBundleClassMorphismTranslatedFamily_eq,
    ← Category.assoc]
  exact congrArg (fun h => h ≫ lineBundleClassMorphism G P R a)
    (lift_fst (fst G T'.obj) (snd G T'.obj ≫ f.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual map over T into the actual pullback of the same P. This is
the original classifying map paired with the unchanged base projection. -/
def lineBundleClassMorphismTranslatedFamilyOver
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    (Over.pullback T.obj.hom).obj G ⟶ (Over.pullback T.obj.hom).obj P.obj :=
  Over.homMk (pullback.lift (lineBundleClassMorphismTranslatedFamily G P R T b a).left
    (pullback.snd G.hom T.obj.hom) (by
      rw [Over.w]
      exact pullback.condition)) (pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The first projection is the original normalized classifying map. -/
@[reassoc (attr := simp)]
theorem lineBundleClassMorphismTranslatedFamilyOver_fst
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    (lineBundleClassMorphismTranslatedFamilyOver G P R T b a).left ≫
      pullback.fst P.obj.hom T.obj.hom =
        (lineBundleClassMorphismTranslatedFamily G P R T b a).left :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The second projection remains the original map to the parameter base. -/
@[reassoc (attr := simp)]
theorem lineBundleClassMorphismTranslatedFamilyOver_snd
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    (lineBundleClassMorphismTranslatedFamilyOver G P R T b a).left ≫
      pullback.snd P.obj.hom T.obj.hom = pullback.snd G.hom T.obj.hom :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The parameter-valued translation law on the ACTUAL maps over T.
This is proved from the all-test cube/classifying equation, not by applying
a field-only base-change theorem to a nonreduced double base. -/
theorem lineBundleClassMorphismTranslatedFamilyOver_eq
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    lineBundleClassMorphismTranslatedFamilyOver G P R T b a =
      (Over.pullback T.obj.hom).map (lineBundleClassMorphism G P R a) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [lineBundleClassMorphismTranslatedFamilyOver, Over.homMk_left, pullback.lift_fst]
    rw [lineBundleClassMorphismTranslatedFamily_eq]
    simp [Over.comp_left]
  · simp [lineBundleClassMorphismTranslatedFamilyOver]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full naturality square over changing locally Noetherian parameter
bases uses the actual original family maps on BOTH G and P. -/
theorem lineBundleClassMorphismTranslatedFamilyOver_naturality
    {T T' : LocallyNoetherianOver (Spec (.of k))} (f : T' ⟶ T)
    (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    (familyScheme G.hom).map f.hom ≫
        (lineBundleClassMorphismTranslatedFamilyOver G P R T b a).left =
      (lineBundleClassMorphismTranslatedFamilyOver G P R T' (f.hom ≫ b) a).left ≫
        (familyScheme P.obj.hom).map f.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, lineBundleClassMorphismTranslatedFamilyOver_fst,
      familyScheme_map_fst]
    rw [← translationFamilyMap_left, ← Over.comp_left,
      lineBundleClassMorphismTranslatedFamily_naturality]
  · simp only [Category.assoc, lineBundleClassMorphismTranslatedFamilyOver_snd,
      familyScheme_map_snd, lineBundleClassMorphismTranslatedFamilyOver_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translation of the class preserves the whole original morphism into
the SAME supplied Picard representative. -/
theorem lineBundleClassMorphism_pullback_translation
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (a : PicardGroup G.left) :
    lineBundleClassMorphism G P R (pullbackClass (GrpObj.mulRight b).hom.left a) =
      lineBundleClassMorphism G P R a := by
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G, LocallyOfFiniteType.isLocallyNoetherian G.hom⟩
  exact congrArg (fun c : normalizedSubgroup G.hom η[G].left (Over.w η[G]) (op G) =>
    ((lineBundleNormalizedRepresentation G P R).homEquiv.symm c : T ⟶ P).hom)
      (normalized_translationFamilyClass_pullback_translation G (𝟙 G) b a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Group inversion pullback preserves the whole line-bundle morphism;
it is not dualization of the line bundle. -/
theorem lineBundleClassMorphism_pullback_inv (a : PicardGroup G.left) :
    lineBundleClassMorphism G P R (pullbackClass ι[G].left a) =
      lineBundleClassMorphism G P R a := by
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G, LocallyOfFiniteType.isLocallyNoetherian G.hom⟩
  exact congrArg (fun c : normalizedSubgroup G.hom η[G].left (Over.w η[G]) (op G) =>
    ((lineBundleNormalizedRepresentation G P R).homEquiv.symm c : T ⟶ P).hom)
      (normalized_translationFamilyClass_pullback_inv G (𝟙 G) a)

/-- The same translation law on the original actual line bundle. -/
theorem lineBundleMorphism_pullback_translation
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (L : LineBundle G.left) :
    lineBundleMorphism G P R (pullbackLineBundle (GrpObj.mulRight b).hom.left L) =
      lineBundleMorphism G P R L := by
  unfold lineBundleMorphism
  rw [← pullbackClass_classOf]
  exact lineBundleClassMorphism_pullback_translation G P R b (classOf _ L)

/-- The same inversion-pullback law on the original actual line bundle. -/
theorem lineBundleMorphism_pullback_inv (L : LineBundle G.left) :
    lineBundleMorphism G P R (pullbackLineBundle ι[G].left L) =
      lineBundleMorphism G P R L := by
  unfold lineBundleMorphism
  rw [← pullbackClass_classOf]
  exact lineBundleClassMorphism_pullback_inv G P R (classOf _ L)

variable [LocallyOfFiniteType P.obj.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Parameter-valued translation factors through the ACTUAL pullback of
the original Pic0. The component realization stays fixed even for a
disconnected or nonreduced parameter base. -/
theorem lineBundleClassMorphismTranslatedFamilyOver_factor_identityComponent
    (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G) (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphismTranslatedFamilyOver G P R T b a =
      (Over.pullback T.obj.hom).map (lineBundleClassMorphismIdentityComponent G P R a) ≫
        (Over.pullback T.obj.hom).map (identityComponentι P.obj) := by
  let := picardCommGrpObj G.hom P R
  rw [← Functor.map_comp, lineBundleClassMorphismIdentityComponent_ι,
    lineBundleClassMorphismTranslatedFamilyOver_eq]

/-- The translation law also holds on the SAME actual Picard identity
component, by its original monic inclusion. -/
theorem lineBundleClassMorphismIdentityComponent_pullback_translation
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphismIdentityComponent G P R (pullbackClass (GrpObj.mulRight b).hom.left a) =
      lineBundleClassMorphismIdentityComponent G P R a := by
  let := picardCommGrpObj G.hom P R
  rw [← cancel_mono (identityComponentι P.obj), lineBundleClassMorphismIdentityComponent_ι,
    lineBundleClassMorphismIdentityComponent_ι, lineBundleClassMorphism_pullback_translation]

/-- The inversion law holds on the original identity component, with no
dual smoothness, properness, dimension or autoduality premise. -/
theorem lineBundleClassMorphismIdentityComponent_pullback_inv (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphismIdentityComponent G P R (pullbackClass ι[G].left a) =
      lineBundleClassMorphismIdentityComponent G P R a := by
  let := picardCommGrpObj G.hom P R
  rw [← cancel_mono (identityComponentι P.obj), lineBundleClassMorphismIdentityComponent_ι,
    lineBundleClassMorphismIdentityComponent_ι, lineBundleClassMorphism_pullback_inv]

/-- Negating the Picard class INVERTS the actual morphism. This is the
operation corresponding to dualizing a bundle, as opposed to inversion pullback. -/
theorem lineBundleClassMorphism_neg (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphism G P R (-a) = (lineBundleClassMorphism G P R a)⁻¹ := by
  let := picardCommGrpObj G.hom P R
  have h := lineBundleClassMorphism_add G P R a (-a)
  rw [add_neg_cancel, lineBundleClassMorphism_zero] at h
  calc
    _ = (lineBundleClassMorphism G P R a)⁻¹ *
        (lineBundleClassMorphism G P R a * lineBundleClassMorphism G P R (-a)) := by
      rw [← _root_.mul_assoc, _root_.inv_mul_cancel, _root_.one_mul]
    _ = _ := by rw [← h, _root_.mul_one]

/-- The sign for dualizing the original line bundle. -/
theorem lineBundleMorphism_dual (L : LineBundle G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleMorphism G P R (dualLineBundle G.left L) = (lineBundleMorphism G P R L)⁻¹ := by
  let := picardCommGrpObj G.hom P R
  unfold lineBundleMorphism
  rw [classOf_dual]
  exact lineBundleClassMorphism_neg G P R (classOf _ L)

variable [IsSeparated P.obj.hom]

/-- Inversion of the SOURCE PARAMETER gives inverse values of the same
original group homomorphism. This is a whole map equation, not a point check. -/
theorem lineBundleClassMorphism_precomp_inv (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    ι[G] ≫ lineBundleClassMorphism G P R a = (lineBundleClassMorphism G P R a)⁻¹ := by
  let := picardCommGrpObj G.hom P R
  let := isMonHom_lineBundleClassMorphism G P R a
  change ι[G] ≫ lineBundleClassMorphism G P R a =
    lineBundleClassMorphism G P R a ≫ ι[P.obj]
  exact GrpObj.inv_hom _

/-- The same parameter-inversion equation in the actual Picard identity
component, retaining its original group law. -/
theorem lineBundleClassMorphismIdentityComponent_precomp_inv (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    ι[G] ≫ lineBundleClassMorphismIdentityComponent G P R a =
      (lineBundleClassMorphismIdentityComponent G P R a)⁻¹ := by
  let := picardCommGrpObj G.hom P R
  let := isMonHom_lineBundleClassMorphismIdentityComponent G P R a
  change ι[G] ≫ lineBundleClassMorphismIdentityComponent G P R a =
    lineBundleClassMorphismIdentityComponent G P R a ≫ ι[identityComponentOver P.obj]
  exact GrpObj.inv_hom _

end AlgebraicGeometry.Scheme.RelativePicard
