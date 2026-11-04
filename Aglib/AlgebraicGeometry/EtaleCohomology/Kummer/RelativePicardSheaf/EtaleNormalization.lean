/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.RepresentedComparison

/-! # Etale sheafification of the original family Picard presheaf

The original normalization has only base Picard classes in its kernel.
Actual pointed open trivializations kill those classes, with no new model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

/-- Every original Picard class is zero on an actual open neighbourhood of a given point. -/
theorem picardClass_pointed_open_zero {T : Scheme.{u}} (a : PicardGroup T) (x : T) :
    ∃ W : T.Opens, x ∈ W ∧ pullbackClass W.ι a = 0 := by
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨W, hx, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
    refine ⟨W, hx, ?_⟩
    exact Quotient.sound ⟨((Scheme.Modules.restrictFunctorIsoPullback W.ι).app L.val).symm ≪≫
      e ≪≫ (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit W.toScheme.ringCatSheaf)).symm⟩

variable {X S : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The unchanged quotient-and-normalization map restricted to the original small etale site. -/
def etaleFamilyNormalization :
    (Scheme.Etale.forget S).op ⋙ familyPicardFunctor p ⟶
      (Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho :=
  Functor.whiskerLeft (Scheme.Etale.forget S).op
    (quotientProjection p ≫ (quotientNormalizedIso p o ho).hom)

/-- The actual normalization kernel vanishes after a pointed open refinement. -/
theorem etaleFamilyNormalization_pointed_kernel_zero (U : S.Etale)
    (a : PicardGroup (pullback p U.hom))
    (ha : (etaleFamilyNormalization p o ho).app (op U) a = 0) (x : U.left) :
    ∃ (V : S.Etale) (v : V ⟶ U) (y : V.left), v.left y = x ∧
      (((Scheme.Etale.forget S).op ⋙ familyPicardFunctor p).map v.op) a = 0 := by
  let T := (Scheme.Etale.forget S).obj U
  have hq : (QuotientAddGroup.mk (a : (familyPicardFunctor p).obj (op T)) :
      (familyPicardFunctor p).obj (op T) ⧸ baseImage p (op T)) = 0 := by
    apply (quotientNormalizedEquiv p o ho (op T)).injective
    change (etaleFamilyNormalization p o ho).app (op U) a =
      (quotientNormalizedEquiv p o ho (op T)) 0
    rw [ha, map_zero]
  obtain ⟨b, hb₀⟩ := (QuotientAddGroup.eq_zero_iff
    (a : (familyPicardFunctor p).obj (op T))).mp hq
  obtain ⟨W, hx, hb⟩ := picardClass_pointed_open_zero b x
  let V : S.Etale := Scheme.Etale.mk (W.ι ≫ U.hom)
  let v : V ⟶ U := MorphismProperty.Over.homMk W.ι rfl (by trivial)
  refine ⟨V, v, ⟨x, hx⟩, rfl, ?_⟩
  change ((familyPicardFunctor p).map ((Scheme.Etale.forget S).map v).op).hom a = 0
  rw [← hb₀]
  have hn := ConcreteCategory.congr_hom
    ((basePullback p).naturality ((Scheme.Etale.forget S).map v).op) b
  refine hn.symm.trans ?_
  change ((basePullback p).app (op ((Scheme.Etale.forget S).obj V))).hom
    (pullbackClass W.ι b) = 0
  rw [hb, map_zero]

/-- Local injectivity uses the original small-etale equalizer sieve. -/
instance etaleFamilyNormalizationIsLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology S)
      (etaleFamilyNormalization p o ho) := by
  apply Scheme.Etale.isLocallyInjective_of_pointed_kernelZero
  intro U a ha x
  exact etaleFamilyNormalization_pointed_kernel_zero p o ho U a ha x

/-- The original normalization is already surjective on each chart. -/
theorem etaleFamilyNormalization_surjective (U : S.Etaleᵒᵖ) :
    Function.Surjective ((etaleFamilyNormalization p o ho).app U) := by
  intro a
  refine ⟨a.val, ?_⟩
  apply Subtype.ext
  change a.val - ((basePullback p).app ((Scheme.Etale.forget S).op.obj U)).hom
    (((originRestriction p o ho).app ((Scheme.Etale.forget S).op.obj U)).hom a.val) = a.val
  rw [show ((originRestriction p o ho).app ((Scheme.Etale.forget S).op.obj U)).hom a.val = 0
    from a.property, map_zero, sub_zero]

/-- An étale family class admits local normalized lifts. -/
instance etaleFamilyNormalizationIsLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology S)
      (etaleFamilyNormalization p o ho) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (etaleFamilyNormalization_surjective p o ho)

variable [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

open Scheme.EtaleCohomology.Kummer

/-- The actual etale sheafification map to the existing normalized Picard sheaf. -/
def familyPicardEtaleToNormalized :
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
      ((Scheme.Etale.forget S).op ⋙ familyPicardFunctor p) ⟶
        normalizedPicardEtaleSheaf p o ho :=
  ((sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).homEquiv
    _ _).symm (etaleFamilyNormalization p o ho)

/-- The actual sheafification map retains the original quotient-normalization unit. -/
theorem familyPicardEtaleToNormalized_unit :
    toSheafify (Scheme.smallEtaleTopology S)
        ((Scheme.Etale.forget S).op ⋙ familyPicardFunctor p) ≫
      (familyPicardEtaleToNormalized p o ho).hom = etaleFamilyNormalization p o ho := by
  exact ((sheafificationAdjunction (Scheme.smallEtaleTopology S)
    AddCommGrpCat.{u + 1}).homEquiv _ _).apply_symm_apply _

/-- The real local trivializations prove the original sheafification map invertible. -/
instance familyPicardEtaleToNormalizedIsIso : IsIso (familyPicardEtaleToNormalized p o ho) := by
  let J := Scheme.smallEtaleTopology S
  let L := presheafToSheaf J AddCommGrpCat.{u + 1}
  let φ := etaleFamilyNormalization p o ho
  have : IsIso (L.map φ) := (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  dsimp only [familyPicardEtaleToNormalized]
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Same source sheafification and same normalized target, with no supplied isomorphism. -/
def familyPicardEtaleSheafificationIso :
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
      ((Scheme.Etale.forget S).op ⋙ familyPicardFunctor p) ≅
        normalizedPicardEtaleSheaf p o ho :=
  asIso (familyPicardEtaleToNormalized p o ho)

end AlgebraicGeometry.Scheme.RelativePicard
