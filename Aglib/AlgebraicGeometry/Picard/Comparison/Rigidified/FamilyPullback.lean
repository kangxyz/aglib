/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified
public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange
public import Aglib.AlgebraicGeometry.Picard.TrivializedPowerTorsor

/-! Transport and comparison of the original rigidified families. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules.Invertible Scheme.Modules.Invertible.TrivializedPowerTorsor

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair

variable {S X S' X' : Scheme.{u}}
  {p : X ⟶ S} {o : S ⟶ X} {ho : o ≫ p = 𝟙 S}
  {p' : X' ⟶ S'} {o' : S' ⟶ X'} {ho' : o' ≫ p' = 𝟙 S'}
  {T : Over S} {T' : Over S'}

/-- The original bundle and frame pull back along an actual family map
that respects the two original origins. This also applies when the base
scheme changes, using the canonical Cartesian family comparison. -/
def mapFamily (f : pullback p' T'.hom ⟶ pullback p T.hom) (g : T'.left ⟶ T.left)
    (h : originSection p' o' ho' T' ≫ f = g ≫ originSection p o ho T)
    (M : RigidifiedPair p o ho T) : RigidifiedPair p' o' ho' T' where
  bundle := pullbackLineBundle f M.bundle
  rigidification :=
    (Scheme.Modules.pullbackComp (originSection p' o' ho' T') f).app M.bundle.val ≪≫
      nativePullFrame M.bundle (originSection p o ho T) (originSection p' o' ho' T' ≫ f)
        g h.symm M.rigidification

set_option backward.isDefEq.respectTransparency false in
/-- The same original family pullback transports the actual rigidified
isomorphism, with its original frame equation. -/
def Iso.mapFamily (f : pullback p' T'.hom ⟶ pullback p T.hom) (g : T'.left ⟶ T.left)
    (h : originSection p' o' ho' T' ≫ f = g ≫ originSection p o ho T)
    {M N : RigidifiedPair p o ho T} (e : Iso M N) :
    Iso (RigidifiedPair.mapFamily (p' := p') (o' := o') (ho' := ho') f g h M)
      (RigidifiedPair.mapFamily (p' := p') (o' := o') (ho' := ho') f g h N) where
  iso := (Scheme.Modules.pullback f).mapIso e.iso
  comm := by
    have h₁ := (Scheme.Modules.pullbackComp (originSection p' o' ho' T') f).hom.naturality
      e.iso.hom
    have h₂ := (Scheme.Modules.pullbackCongr h.symm).inv.naturality e.iso.hom
    have h₃ := (Scheme.Modules.pullbackComp g (originSection p o ho T)).inv.naturality e.iso.hom
    simp only [Functor.comp_map] at h₁ h₂ h₃
    simp only [RigidifiedPair.mapFamily, nativePullFrame, CategoryTheory.Iso.trans_hom,
      CategoryTheory.Iso.app_hom, CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.app_inv,
      CategoryTheory.Functor.mapIso_hom]
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, ← Functor.map_comp_assoc, e.comm]

/-- The two original origin sections match under the original family
base-change comparison. The lifted origin is the existing origin section
over the new base, evaluated on that base itself. -/
theorem originSection_comp_familyBaseChangeIso (b : S' ⟶ S) (U : Over S') :
    let v := originSection p o ho (Over.mk b)
    let hv := originSection_snd p o ho (Over.mk b)
    originSection (pullback.snd p b) v hv U ≫ (familyBaseChangeIso p b U).hom =
      originSection p o ho ((Over.map b).obj U) := by
  let v := originSection p o ho (Over.mk b)
  let hv := originSection_snd p o ho (Over.mk b)
  let a := originSection (pullback.snd p b) v hv U
  let z := originSection p o ho ((Over.map b).obj U)
  let e := familyBaseChangeIso p b U
  have h : a ≫ e.hom = z := by
    apply pullback.hom_ext
    · change (a ≫ e.hom) ≫ pullback.fst p (U.hom ≫ b) =
        z ≫ pullback.fst p (U.hom ≫ b)
      rw [Category.assoc, familyBaseChangeIso_hom_fst, ← Category.assoc,
        originSection_fst, Category.assoc]
      change U.hom ≫ v ≫ pullback.fst p b = z ≫ pullback.fst p (U.hom ≫ b)
      have hv' : v ≫ pullback.fst p b = b ≫ o := originSection_fst p o ho (Over.mk b)
      have hz : z ≫ pullback.fst p (U.hom ≫ b) = (U.hom ≫ b) ≫ o :=
        originSection_fst p o ho ((Over.map b).obj U)
      exact (congrArg (fun g => U.hom ≫ g) hv').trans
        ((Category.assoc U.hom b o).symm.trans hz.symm)
    · change (a ≫ e.hom) ≫ pullback.snd p (U.hom ≫ b) =
        z ≫ pullback.snd p (U.hom ≫ b)
      rw [Category.assoc, familyBaseChangeIso_hom_snd, originSection_snd]
      exact (originSection_snd p o ho ((Over.map b).obj U)).symm
  exact h

/-- Transport an original rigidified pair to the actual scalar-extended
family, through its original Cartesian family comparison. -/
def mapBaseChange (b : S' ⟶ S) (U : Over S')
    (M : RigidifiedPair p o ho ((Over.map b).obj U)) :
    RigidifiedPair (pullback.snd p b) (originSection p o ho (Over.mk b))
      (originSection_snd p o ho (Over.mk b)) U :=
  mapFamily (p := p) (o := o) (ho := ho) (T := (Over.map b).obj U) (T' := U)
    (familyBaseChangeIso p b U).hom (𝟙 U.left)
    ((originSection_comp_familyBaseChangeIso (ho := ho) b U).trans
      (Category.id_comp _).symm) M

end AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair
