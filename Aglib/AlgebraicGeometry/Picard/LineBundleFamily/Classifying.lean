/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Normalized
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Mathlib.CategoryTheory.Yoneda

/-!
# Classifying morphisms of normalized line-bundle families

For a representation of the existing normalized Picard functor, the classifying
morphism is the inverse of its natural Hom equivalence. The equations below
identify the class of the original family, arbitrary test-scheme pullback, the
zero family and the universal family. Locally Noetherian test schemes need not
be reduced. Representability is an explicit construction input in this leaf;
geometric suppliers belong to the projective Picard scheme construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  {P : LocallyNoetherianOver S}
  (R : ((locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor p o ho ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The classifying morphism of an actual family class, normalized along the
specified section. -/
def normalizedFamilyClassifyingMap (T : LocallyNoetherianOver S)
    (a : PicardGroup (pullback p T.obj.hom)) : T ⟶ P :=
  R.homEquiv.symm (normalizedFamilyClass p o ho T.obj a)

theorem homEquiv_normalizedFamilyClassifyingMap (T : LocallyNoetherianOver S)
    (a : PicardGroup (pullback p T.obj.hom)) :
    R.homEquiv (normalizedFamilyClassifyingMap p o ho R T a) =
      normalizedFamilyClass p o ho T.obj a :=
  R.homEquiv.apply_symm_apply _

/-- The original bundle class attached to the classifying morphism is
`a - pr₂^*(o_T^* a)`. -/
theorem homEquiv_normalizedFamilyClassifyingMap_val (T : LocallyNoetherianOver S)
    (a : PicardGroup (pullback p T.obj.hom)) :
    (R.homEquiv (normalizedFamilyClassifyingMap p o ho R T a)).val =
      a - pullbackClass (pullback.snd p T.obj.hom)
        (pullbackClass (originSection p o ho T.obj) a) := by
  rw [homEquiv_normalizedFamilyClassifyingMap, normalizedFamilyClass_val]

/-- The classifying morphism commutes with the original family pullback for
every morphism of locally Noetherian test schemes, including nilpotent tests. -/
theorem normalizedFamilyClassifyingMap_pullback {T T' : LocallyNoetherianOver S}
    (f : T' ⟶ T) (a : PicardGroup (pullback p T.obj.hom)) :
    normalizedFamilyClassifyingMap p o ho R T'
        (pullbackClass ((familyScheme p).map f.hom) a) =
      f ≫ normalizedFamilyClassifyingMap p o ho R T a := by
  apply R.homEquiv.injective
  rw [R.homEquiv_comp, homEquiv_normalizedFamilyClassifyingMap,
    homEquiv_normalizedFamilyClassifyingMap]
  exact normalizedFamilyClass_pullback p o ho f.hom a

/-- Equality with the classifying morphism of the zero family is precisely
vanishing of the normalized class, as a scheme-valued assertion. -/
theorem normalizedFamilyClassifyingMap_eq_zero_iff (T : LocallyNoetherianOver S)
    (a : PicardGroup (pullback p T.obj.hom)) :
    normalizedFamilyClassifyingMap p o ho R T a =
        normalizedFamilyClassifyingMap p o ho R T 0 ↔
      normalizedFamilyClass p o ho T.obj a = 0 := by
  rw [← R.homEquiv.injective.eq_iff, homEquiv_normalizedFamilyClassifyingMap,
    homEquiv_normalizedFamilyClassifyingMap, normalizedFamilyClass_zero]
  rfl

/-- The universal normalized class for the same selected representation. -/
def normalizedUniversalClass : normalizedSubgroup p o ho (op P.obj) :=
  R.homEquiv (𝟙 P)

/-- Pulling the universal class back by the actual classifying morphism gives
the normalized class of the original family. -/
theorem pullback_normalizedUniversalClass (T : LocallyNoetherianOver S)
    (a : PicardGroup (pullback p T.obj.hom)) :
    pullbackClass ((familyScheme p).map
      (normalizedFamilyClassifyingMap p o ho R T a).hom)
        (normalizedUniversalClass p o ho R).val =
      (normalizedFamilyClass p o ho T.obj a).val := by
  have h := R.homEquiv_comp (normalizedFamilyClassifyingMap p o ho R T a) (𝟙 P)
  rw [Category.comp_id, homEquiv_normalizedFamilyClassifyingMap] at h
  exact (congrArg Subtype.val h).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem normalizedFamilyClassifyingMap_universal :
    normalizedFamilyClassifyingMap p o ho R P (normalizedUniversalClass p o ho R).val =
      𝟙 P := by
  change R.homEquiv.symm (normalizedFamilyClass p o ho P.obj
    (normalizedUniversalClass p o ho R).val) = 𝟙 P
  rw [normalizedFamilyClass_normalized]
  exact R.homEquiv.symm_apply_apply _

end AlgebraicGeometry.Scheme.RelativePicard
