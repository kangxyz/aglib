/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Normalized
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal

/-!
# Set-valued relative Picard classes from the native group functors

These are forgetful composites of the native Picard, normalized-kernel and
quotient functors. No second Picard object or pullback implementation is used.
The original `R5Lab.Aglib.AlgebraicGeometry.Picard.Relative.Basic` interface,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, used a `pullback.lift`
transition map. Its equality with the actual native `pullback.map` is proved
below. The original and new bases and all test schemes are arbitrary.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.RelativePicard.Classes
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable {S X : Scheme.{u}}

abbrev basePicardFunctor (S : Scheme.{u}) :=
  Scheme.RelativePicard.basePicardFunctor S ⋙ CategoryTheory.forget AddCommGrpCat

abbrev familyPicardFunctor (p : X ⟶ S) :=
  Scheme.RelativePicard.familyPicardFunctor p ⋙ CategoryTheory.forget AddCommGrpCat

abbrev basePullback (p : X ⟶ S) :=
  Functor.whiskerRight (Scheme.RelativePicard.basePullback p) (CategoryTheory.forget AddCommGrpCat)

variable (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

abbrev originSection := Scheme.RelativePicard.originSection p o ho

@[reassoc (attr := simp)] theorem originSection_snd (T : Over S) :
    originSection p o ho T ≫ pullback.snd p T.hom = 𝟙 _ :=
  Scheme.RelativePicard.originSection_snd p o ho T

/-- The source lift formula and the native map of the family are the same arrow. -/
theorem familyMap_eq_familyScheme_map {T T' : Over S} (f : T' ⟶ T) :
    Scheme.Hom.familyMap p T.hom T'.hom f.left (Over.w f) =
      (RelativePicard.familyScheme p).map f := by
  apply pullback.hom_ext <;> simp

@[reassoc] theorem originSection_naturality {T T' : Over S} (f : T' ⟶ T) :
    originSection p o ho T' ≫ Scheme.Hom.familyMap p T.hom T'.hom f.left (Over.w f) =
      f.left ≫ originSection p o ho T := by
  rw [familyMap_eq_familyScheme_map]
  exact ((RelativePicard.originSectionNatTrans p o ho).naturality f).symm

abbrev originRestriction :=
  Functor.whiskerRight (Scheme.RelativePicard.originRestriction p o
      ho) (CategoryTheory.forget AddCommGrpCat)

@[simp] theorem basePullback_originRestriction :
    basePullback p ≫ originRestriction p o ho = 𝟙 (basePicardFunctor S) := by
  exact congrArg (fun t ↦ Functor.whiskerRight t (CategoryTheory.forget AddCommGrpCat))
    (Scheme.RelativePicard.basePullback_originRestriction p o ho)

include o ho in
theorem basePullback_injective (T : Over S) :
    Function.Injective ((basePullback p).app (op T)) :=
  RelativePicard.basePullback_app_injective p o ho (op T)

abbrev normalizedClassFunctor :=
  RelativePicard.normalizedPicardFunctor p o ho ⋙ CategoryTheory.forget AddCommGrpCat

abbrev normalizedInclusion :=
  Functor.whiskerRight (Scheme.RelativePicard.normalizedInclusion p o
      ho) (CategoryTheory.forget AddCommGrpCat)

def normalizedZero (T : Over S) : (normalizedClassFunctor p o ho).obj (op T) := 0

@[simp] theorem normalizedZero_naturality {T T' : Over S} (f : T' ⟶ T) :
    (normalizedClassFunctor p o ho).map f.op (normalizedZero p o ho T) =
      normalizedZero p o ho T' :=
  map_zero ((RelativePicard.normalizedPicardFunctor p o ho).map f.op).hom

end AlgebraicGeometry.Scheme.RelativePicard.Classes
