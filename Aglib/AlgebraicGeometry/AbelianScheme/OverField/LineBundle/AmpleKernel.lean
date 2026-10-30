/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.KernelClass
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Proper
public import Aglib.AlgebraicGeometry.Group.Kernel.Basic

/-!
# The scheme-theoretic kernel of an ample line-bundle morphism is finite

The normalized family vanishes on the full kernel. Its anti-diagonal pullback
trivializes the tensor of the restricted ample bundle with its inverse-parameter
pullback. This tensor is ample, and the kernel is proper, hence finite. No
reduction, tangent-space argument, dual smoothness or dual dimension is used.

This is the argument of Edixhoven--van der Geer--Moonen, Chapter II, (2.17)(iii)
and (2.19), applied directly to the full group-scheme kernel.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- Every closed scheme-valued family in the zero fibre of an ample
line-bundle morphism is finite over the original field. -/
theorem isFinite_of_isClosedImmersion_of_comp_lineBundleMorphism_eq_one
    (T : LocallyNoetherianOver (Spec (.of k))) (t : T.obj ⟶ G)
    [IsClosedImmersion t.left] (L : LineBundle G.left) (hL : L.IsAmple)
    (ht : letI := picardCommGrpObj G.hom P R
      t ≫ lineBundleMorphism G P R L = 1) : IsFinite T.obj.hom := by
  have : IsProper T.obj.hom := by rw [← Over.w t]; infer_instance
  have : T.obj.left.IsSeparated := ⟨by rw [← terminal.comp_from T.obj.hom]; infer_instance⟩
  have : IsIso ι[G].left := (Over.forget (Spec (.of k))).map_isIso ι[G]
  have : IsAffineHom t⁻¹.left := by
    change IsAffineHom (t ≫ ι[G]).left
    rw [Over.comp_left]
    infer_instance
  have hpos := (hL.pullback_of_isAffineHom t.left).tensor
    (hL.pullback_of_isAffineHom t⁻¹.left)
  apply hpos.isFinite_of_isProper_of_classOf_eq_zero T.obj.hom
  rw [classOf_tensor, ← pullbackClass_classOf, ← pullbackClass_classOf]
  exact pullbackClass_add_inverse_eq_zero_of_comp_lineBundleClassMorphism_eq_one
    G P R t (classOf G.left L) ht

variable [IsSeparated P.obj.hom]

/-- Bundle the original morphism between the original group objects, for
the existing scheme-theoretic kernel construction. -/
def lineBundleClassGroupHom (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    Grp.mk G ⟶ Grp.mk P.obj :=
  letI := picardCommGrpObj G.hom P R
  letI := isMonHom_lineBundleClassMorphism G P R a
  Grp.ofHom (lineBundleClassMorphism G P R a)

/-- The actual group-scheme kernel of `φ_L` is finite for an ample `L`,
including its nilpotent structure. The dual Picard component need not yet
be known smooth, proper or of a prescribed dimension. -/
theorem isFinite_kernel_lineBundleClassGroupHom (L : LineBundle G.left)
    (hL : L.IsAmple) :
    IsFinite (Group.Kernel.group (lineBundleClassGroupHom G P R (classOf G.left L))).X.hom := by
  let := picardCommGrpObj G.hom P R
  let f := lineBundleClassGroupHom G P R (classOf G.left L)
  let K := Group.Kernel.group f
  let t : K.X ⟶ G := (Group.Kernel.inclusion f).hom.hom
  have : IsClosedImmersion t.left :=
    MorphismProperty.of_isPullback (Group.Kernel.schemeSquare f).flip inferInstance
  have : IsProper K.X.hom := by rw [← Over.w t]; infer_instance
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨K.X, LocallyOfFiniteType.isLocallyNoetherian K.X.hom⟩
  have ht : t ≫ lineBundleMorphism G P R L = 1 := (Group.Kernel.square f).w
  exact isFinite_of_isClosedImmersion_of_comp_lineBundleMorphism_eq_one G P R T t L hL ht

/-- Bundle the same original morphism after its actual identity-component
factorization, with that component's original group law. -/
def lineBundleClassIdentityComponentGroupHom (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    Grp.mk G ⟶ Grp.mk (Group.identityComponentOver P.obj) :=
  letI := picardCommGrpObj G.hom P R
  letI := isMonHom_lineBundleClassMorphismIdentityComponent G P R a
  Grp.ofHom (lineBundleClassMorphismIdentityComponent G P R a)

/-- Finiteness also concerns the actual kernel of the map into the actual
`Pic⁰` component. It does not require any dual abelian-variety theorem. -/
theorem isFinite_kernel_lineBundleClassIdentityComponentGroupHom
    (L : LineBundle G.left) (hL : L.IsAmple) :
    IsFinite (Group.Kernel.group
      (lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L))).X.hom := by
  let := picardCommGrpObj G.hom P R
  let f := lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L)
  let K := Group.Kernel.group f
  let t : K.X ⟶ G := (Group.Kernel.inclusion f).hom.hom
  have : IsSeparated (Group.identityComponentOver P.obj).hom := by
    change IsSeparated ((Group.identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  have : IsClosedImmersion t.left :=
    MorphismProperty.of_isPullback (Group.Kernel.schemeSquare f).flip inferInstance
  have : IsProper K.X.hom := by rw [← Over.w t]; infer_instance
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨K.X, LocallyOfFiniteType.isLocallyNoetherian K.X.hom⟩
  have ht₀ : t ≫ lineBundleClassMorphismIdentityComponent G P R (classOf G.left L) = 1 :=
    (Group.Kernel.square f).w
  have ht : t ≫ lineBundleMorphism G P R L = 1 := by
    change t ≫ lineBundleClassMorphism G P R (classOf G.left L) = 1
    rw [← lineBundleClassMorphismIdentityComponent_ι, ← Category.assoc, ht₀]
    simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]
  exact isFinite_of_isClosedImmersion_of_comp_lineBundleMorphism_eq_one G P R T t L hL ht

end AlgebraicGeometry.Scheme.RelativePicard
