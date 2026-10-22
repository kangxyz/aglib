/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteTypeApproximation
public import Aglib.AlgebraicGeometry.IdealSheaf.FinitePresentation
public import Aglib.AlgebraicGeometry.IdealSheaf.Limits
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Actual finite-presentation closed-superscheme approximation

On a qcqs ambient scheme, the original closed subscheme is the limit of the closed
superschemes defined by its actual finite-type subideals. The stage structure maps
are locally of finite presentation and closed immersions, hence quasicompact and
quasiseparated. Transition maps are closed immersions. The stages are not asserted
to have equal support or to be nilpotent thickenings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Forget the finite-type and ambient-containment proofs, retaining the actual ideal. -/
def finiteTypeSubidealForget : FiniteTypeSubideal I ⥤ X.IdealSheafData where
  obj J := J.val
  map f := homOfLE f.le

/-- The cofiltered diagram of actual finite-presentation closed superschemes over X. -/
def finitePresentationApproximationDiagram : (FiniteTypeSubideal I)ᵒᵖ ⥤ Over X :=
  (finiteTypeSubidealForget I).op ⋙ subschemeFunctor X

/-- The original closed subscheme, with its canonical inclusions into all stages. -/
def finitePresentationApproximationCone : Cone (finitePresentationApproximationDiagram I) where
  pt := Over.mk I.subschemeι
  π :=
    { app J := Over.homMk (inclusion J.unop.property.1)
        (inclusion_subschemeι J.unop.property.1)
      naturality _J K _f := hom_ext_subscheme K.unop.val _ _ }

/-- Every stage is locally of finite presentation over the original ambient scheme. -/
instance finitePresentationApproximation_obj_locallyOfFinitePresentation
    (J : (FiniteTypeSubideal I)ᵒᵖ) :
    LocallyOfFinitePresentation ((finitePresentationApproximationDiagram I).obj J).hom :=
  J.unop.val.locallyOfFinitePresentation_subschemeι_iff.mpr J.unop.property.2

/-- The stage structure maps are actual closed immersions. -/
instance finitePresentationApproximation_obj_isClosedImmersion
    (J : (FiniteTypeSubideal I)ᵒᵖ) :
    IsClosedImmersion ((finitePresentationApproximationDiagram I).obj J).hom := by
  change IsClosedImmersion J.unop.val.subschemeι
  infer_instance

/-- Every transition is an actual closed immersion, in particular an affine morphism. -/
instance finitePresentationApproximation_map_isClosedImmersion
    {J K : (FiniteTypeSubideal I)ᵒᵖ} (f : J ⟶ K) :
    IsClosedImmersion ((finitePresentationApproximationDiagram I).map f).left := by
  let g := (finitePresentationApproximationDiagram I).map f
  have : IsClosedImmersion (g.left ≫ ((finitePresentationApproximationDiagram I).obj K).hom) := by
    rw [Over.w g]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion g.left
    ((finitePresentationApproximationDiagram I).obj K).hom

/-- The actual closed-superscheme approximation cone is limiting over X. -/
def finitePresentationApproximationConeIsLimit [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLimit (finitePresentationApproximationCone I) := by
  have hsup : (⨆ J : (FiniteTypeSubideal I)ᵒᵖ, J.unop.val) = I := by
    apply le_antisymm
    · exact iSup_le fun J => J.unop.property.1
    · calc
        I = ⨆ J : FiniteTypeSubideal I, J.val := (iSup_finiteTypeSubideal I).symm
        _ ≤ ⨆ K : (FiniteTypeSubideal I)ᵒᵖ, K.unop.val :=
          iSup_le fun J => le_iSup (fun K : (FiniteTypeSubideal I)ᵒᵖ => K.unop.val) (op J)
  let e : (subschemeSupCone (finiteTypeSubidealForget I).op).pt ≅
      (finitePresentationApproximationCone I).pt :=
    eqToIso (congrArg (fun J : X.IdealSheafData => Over.mk J.subschemeι) hsup)
  exact (subschemeSupConeIsLimit (finiteTypeSubidealForget I).op).ofIsoLimit
    (Cone.ext e (fun J => hom_ext_subscheme J.unop.val _ _))

/-- The same actual diagram, viewed in schemes. -/
def finitePresentationApproximationSchemeDiagram : (FiniteTypeSubideal I)ᵒᵖ ⥤ Scheme :=
  finitePresentationApproximationDiagram I ⋙ Over.forget X

/-- The actual scheme cone has the original closed subscheme, not a chosen isomorphic
replacement, as its point. -/
def finitePresentationApproximationSchemeCone :
    Cone (finitePresentationApproximationSchemeDiagram I) :=
  (Over.forget X).mapCone (finitePresentationApproximationCone I)

@[simp] theorem finitePresentationApproximationSchemeCone_pt :
    (finitePresentationApproximationSchemeCone I).pt = I.subscheme := rfl

@[simp] theorem finitePresentationApproximationSchemeCone_π_app
    (J : (FiniteTypeSubideal I)ᵒᵖ) :
    (finitePresentationApproximationSchemeCone I).π.app J = inclusion J.unop.property.1 := rfl

/-- The original closed subscheme is the actual inverse limit of its finite-presentation
closed-superscheme approximation. -/
def finitePresentationApproximationSchemeConeIsLimit
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLimit (finitePresentationApproximationSchemeCone I) := by
  let : IsConnected (FiniteTypeSubideal I)ᵒᵖ :=
    IsCofiltered.isConnected (FiniteTypeSubideal I)ᵒᵖ
  exact isLimitOfPreserves (Over.forget X) (finitePresentationApproximationConeIsLimit I)

end AlgebraicGeometry.Scheme.IdealSheafData
