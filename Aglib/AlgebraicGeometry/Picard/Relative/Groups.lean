/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Relative.Classes
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Properties

/-!
# Native group-valued Picard compatibility

The incoming R5 relative-group interface at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690` delegates to the native additive
Picard pullbacks, quotient and normalization. Its historical tensor theorem
argument is retained for callers; the native maps have unconditional proofs.
The relative quotient transition maps are the canonical quotient maps and
require no section. The section is used only to normalize. All test schemes,
including nonreduced and non-Noetherian schemes, are allowed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.RelativePicard.Classes
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable {S X : Scheme.{u}}

abbrev basePicardGroupFunctor (_htensor : ModuleTensorPullback.{u}) (S : Scheme.{u}) :=
  Scheme.RelativePicard.basePicardFunctor S

abbrev familyPicardGroupFunctor (_htensor : ModuleTensorPullback.{u}) (p : X ⟶ S) :=
  Scheme.RelativePicard.familyPicardFunctor p

variable (htensor : ModuleTensorPullback.{u}) (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

abbrev basePullbackHom (_htensor : ModuleTensorPullback.{u}) (p : X ⟶ S) (T : Over S) :=
  ((Scheme.RelativePicard.basePullback p).app (op T)).hom
abbrev originRestrictionHom (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (T : Over S) :=
  ((Scheme.RelativePicard.originRestriction p o ho).app (op T)).hom

theorem origin_base_comp (T : Over S) :
    (originRestrictionHom htensor p o ho T).comp (basePullbackHom htensor p T) =
      AddMonoidHom.id _ :=
  Scheme.RelativePicard.originRestriction_comp_basePullback p o ho (op T)

abbrev normalizedGroup (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (T : Over S) :=
  Scheme.RelativePicard.normalizedSubgroup p o ho (op T)

abbrev normalizedMap (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) {T T' : Over S} (f : T' ⟶ T) :=
  ((Scheme.RelativePicard.normalizedPicardFunctor p o ho).map f.op).hom

abbrev normalizedGroupFunctor (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) :=
  Scheme.RelativePicard.normalizedPicardFunctor p o ho

abbrev normalizeHom (T : Over S) :=
  Scheme.RelativePicard.Split.normalize (basePullbackHom htensor p T)
    (originRestrictionHom htensor p o ho T) (origin_base_comp htensor p o ho T)

@[simp] theorem normalizeHom_val (T : Over S) (a : PicardGroup (pullback p T.hom)) :
    (normalizeHom htensor p o ho T a).val = a -
      pullbackClass (pullback.snd p T.hom) (pullbackClass (originSection p o ho T) a) := rfl

/-- Normalization commutes with the original transition map on every test scheme. -/
theorem normalizeHom_naturality {T T' : Over S} (f : T' ⟶ T)
    (a : PicardGroup (pullback p T.hom)) :
    normalizedMap htensor p o ho f (normalizeHom htensor p o ho T a) =
      normalizeHom htensor p o ho T' ((familyPicardFunctor p).map f.op a) := by
  have h := congrArg (fun φ => φ.hom (QuotientAddGroup.mk a))
    ((Scheme.RelativePicard.quotientNormalizedIso p o ho).hom.naturality f.op)
  exact h.symm

abbrev relativeQuotientGroup (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (T : Over S) :=
  (Scheme.RelativePicard.relativePicardFunctor p).obj (op T)

abbrev quotientNormalizedEquiv (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (T : Over S) :=
  Scheme.RelativePicard.quotientNormalizedEquiv p o ho (op T)

@[simp] theorem quotientNormalizedEquiv_mk (T : Over S)
    (a : PicardGroup (pullback p T.hom)) :
    quotientNormalizedEquiv htensor p o ho T (QuotientAddGroup.mk a) =
      normalizeHom htensor p o ho T a := rfl

abbrev relativeQuotientMap (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (_o : S ⟶ X) (_ho : _o ≫ p = 𝟙 S) {T T' : Over S} (f : T' ⟶ T) :=
  ((Scheme.RelativePicard.relativePicardFunctor p).map f.op).hom

@[simp] theorem relativeQuotientMap_mk {T T' : Over S} (f : T' ⟶ T)
    (a : PicardGroup (pullback p T.hom)) :
    relativeQuotientMap htensor p o ho f (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk ((familyPicardFunctor p).map f.op a) :=
  Scheme.RelativePicard.relativePicardFunctor_map_mk p f.op a

abbrev relativeQuotientGroupFunctor (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (_o : S ⟶ X) (_ho : _o ≫ p = 𝟙 S) :=
  Scheme.RelativePicard.relativePicardFunctor p
abbrev quotientNormalizedIso (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) :=
  Scheme.RelativePicard.quotientNormalizedIso p o ho
abbrev quotientProjection (_htensor : ModuleTensorPullback.{u})
    (p : X ⟶ S) (_o : S ⟶ X) (_ho : _o ≫ p = 𝟙 S) :=
  Scheme.RelativePicard.quotientProjection p

/-- Forgetting the native group structure is literally the native class functor. -/
def normalizedForgetIso :
    normalizedGroupFunctor htensor p o ho ⋙ CategoryTheory.forget AddCommGrpCat ≅
    normalizedClassFunctor p o ho := Iso.refl _

end AlgebraicGeometry.Scheme.RelativePicard.Classes
