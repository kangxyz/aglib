/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Normalized

/-!
# Normalization of an actual line-bundle family

For the existing family `X ×_S T`, normalization sends its actual Picard class `a`
to `a - pr₂^*(o_T^* a)`. This is a natural additive projection, on all test
schemes, including nonreduced ones. Its kernel is exactly the classes pulled
back from the base. The line-bundle constructor uses the same tensor, dual and
pullback operations as that equation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- Normalization is the quotient projection followed by the existing split
identification with the kernel of origin restriction. -/
def familyNormalization : familyPicardFunctor p ⟶ normalizedPicardFunctor p o ho :=
  quotientProjection p ≫ (quotientNormalizedIso p o ho).hom

/-- The normalized class of an actual family. -/
def normalizedFamilyClass (T : Over S) :
    PicardGroup (pullback p T.hom) →+ normalizedSubgroup p o ho (op T) :=
  ((familyNormalization p o ho).app (op T)).hom

theorem normalizedFamilyClass_val (T : Over S) (a : PicardGroup (pullback p T.hom)) :
    (normalizedFamilyClass p o ho T a).val =
      a - pullbackClass (pullback.snd p T.hom)
        (pullbackClass (originSection p o ho T) a) := rfl

/-- Normalization commutes with the original family pullback along every
morphism of test schemes. -/
theorem normalizedFamilyClass_pullback {T T' : Over S} (f : T' ⟶ T)
    (a : PicardGroup (pullback p T.hom)) :
    normalizedFamilyClass p o ho T' (pullbackClass ((familyScheme p).map f) a) =
      ((normalizedPicardFunctor p o ho).map f.op).hom
        (normalizedFamilyClass p o ho T a) := by
  exact congrArg (fun φ => φ.hom a) ((familyNormalization p o ho).naturality f.op)

@[simp]
theorem normalizedFamilyClass_zero (T : Over S) :
    normalizedFamilyClass p o ho T 0 = 0 := map_zero _

@[simp]
theorem normalizedFamilyClass_normalized (T : Over S)
    (a : normalizedSubgroup p o ho (op T)) :
    normalizedFamilyClass p o ho T a.val = a :=
  Split.normalize_on_ker _ _ (originRestriction_comp_basePullback p o ho (op T)) a

/-- A family has zero normalized class exactly when its original class is
the pullback of its origin restriction. No fibrewise criterion is used. -/
theorem normalizedFamilyClass_eq_zero_iff (T : Over S)
    (a : PicardGroup (pullback p T.hom)) :
    normalizedFamilyClass p o ho T a = 0 ↔
      a = pullbackClass (pullback.snd p T.hom)
        (pullbackClass (originSection p o ho T) a) := by
  constructor
  · intro h
    exact sub_eq_zero.mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact sub_eq_zero.mpr h

/-- If both the normalized family and its origin restriction vanish, the
original line-bundle class vanishes. -/
theorem eq_zero_of_normalizedFamilyClass_eq_zero (T : Over S)
    (a : PicardGroup (pullback p T.hom))
    (ha : normalizedFamilyClass p o ho T a = 0)
    (ho' : pullbackClass (originSection p o ho T) a = 0) : a = 0 := by
  rw [(normalizedFamilyClass_eq_zero_iff p o ho T a).mp ha, ho']
  exact map_zero (pullbackHom _)

/-- The actual normalized line bundle `L ⊗ (pr₂^* o_T^* L)⁻¹`. -/
def normalizedFamilyLineBundle (T : Over S) (L : LineBundle (pullback p T.hom)) :
    LineBundle (pullback p T.hom) :=
  tensorLineBundle _ L (dualLineBundle _
    (pullbackLineBundle (pullback.snd p T.hom)
      (pullbackLineBundle (originSection p o ho T) L)))

/-- Normalization of actual bundles agrees with the original Picard-group
normalization, with no auxiliary bundle model. -/
theorem classOf_normalizedFamilyLineBundle (T : Over S)
    (L : LineBundle (pullback p T.hom)) :
    classOf _ (normalizedFamilyLineBundle p o ho T L) =
      (normalizedFamilyClass p o ho T (classOf _ L)).val := by
  simp only [normalizedFamilyLineBundle, classOf_tensor, classOf_dual,
    ← pullbackClass_classOf, normalizedFamilyClass_val, sub_eq_add_neg]

end AlgebraicGeometry.Scheme.RelativePicard
