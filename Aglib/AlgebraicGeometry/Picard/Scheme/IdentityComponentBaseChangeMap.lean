/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.FieldProperties

/-!
# The structure-map triangle of the native Picard identity-component base change

The existing `picardIdentityComponentBaseChangeIso` identifies the base change of the actual
Picard identity component with the identity component of the base-changed representative. This
file proves its whole structure-map triangle over the extension field, using the original
native isomorphism and the original pullback projection. The current consumer is properness
descent of the Jacobian over an arbitrary field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (K : Type u) [Field K] [Algebra k K]

/-- The actual native component comparison preserves the whole structure morphism to the
extension field. Thus its scheme isomorphism is compatible with the original pullback map. -/
@[reassoc]
theorem picardIdentityComponentBaseChangeIso_hom_comp :
    (picardIdentityComponentBaseChangeIso p P R K).hom ≫
        (picardIdentityComponent
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P)
          (baseChangeRepresentableBy p (Spec.map (CommRingCat.ofHom (algebraMap k K))) P R)).hom =
      pullback.snd (picardIdentityComponent p P R).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let := picardCommGrpObj p P R
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  change
    (((isPullback_preimage_identityComponent P.obj K).isoPullback.inv ≫
        (Scheme.isoOfEq (pullback P.obj.hom b)
          (identityComponent_pullback P.obj K).symm).hom) ≫
      (Scheme.isoOfEq ((Over.pullback b).obj P.obj).left
        ((picardIdentityComponent_pullback p P R K).trans
          (identityComponent_baseChangeRepresentableBy p P R K).symm)).hom) ≫
      (picardIdentityComponent (pullback.snd p b) (LocallyNoetherianOver.baseChange b P)
        (baseChangeRepresentableBy p b P R)).hom =
      pullback.snd ((identityComponent P.obj).ι ≫ P.obj.hom) b
  simp only [picardIdentityComponent, Group.identityComponentOver_hom,
    Over.pullback_obj_hom]
  have h₂ := Scheme.isoOfEq_hom_ι_assoc ((Over.pullback b).obj P.obj).left
    ((picardIdentityComponent_pullback p P R K).trans
      (identityComponent_baseChangeRepresentableBy p P R K).symm)
    (pullback.snd P.obj.hom b)
  have h₁ := Scheme.isoOfEq_hom_ι_assoc (pullback P.obj.hom b)
    (identityComponent_pullback P.obj K).symm (pullback.snd P.obj.hom b)
  simp only [Category.assoc]
  rw [h₂, h₁]
  exact (isPullback_preimage_identityComponent P.obj K).isoPullback_inv_snd

end AlgebraicGeometry.Scheme.RelativePicard
