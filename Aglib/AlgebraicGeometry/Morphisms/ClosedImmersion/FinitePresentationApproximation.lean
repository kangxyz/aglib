/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.FinitePresentationApproximation

/-!
# Finite-presentation closed approximation with the original source as apex

A closed immersion into a qcqs scheme is the limit of the finite-presentation
closed superschemes defined by finite-type subideals of its native kernel.
The cone has the literal original source, with the actual map to its image
followed by the canonical ideal inclusions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (e : X ⟶ Y)

/-- The actual finite-presentation closed-superscheme diagram of the native kernel. -/
def finitePresentationApproximationDiagram :
    (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ ⥤ Scheme :=
  e.ker.finitePresentationApproximationSchemeDiagram

/-- Each actual stage retains its canonical structural map to the ambient scheme. -/
def finitePresentationApproximationStructure :
    e.finitePresentationApproximationDiagram ⟶
      (Functor.const (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ).obj Y where
  app J := J.unop.val.subschemeι
  naturality J K f := by
    change ((e.ker.finitePresentationApproximationDiagram).map f).left ≫
      K.unop.val.subschemeι = J.unop.val.subschemeι ≫ 𝟙 Y
    rw [Category.comp_id]
    exact Over.w ((e.ker.finitePresentationApproximationDiagram).map f)

/-- The cone with the literal original source and actual image-factorization maps. -/
def finitePresentationApproximationCone : Cone e.finitePresentationApproximationDiagram :=
  e.ker.finitePresentationApproximationSchemeCone.extend e.toImage

@[simp] lemma finitePresentationApproximationCone_pt :
    e.finitePresentationApproximationCone.pt = X := rfl

@[simp] lemma finitePresentationApproximationCone_π_app
    (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) :
    e.finitePresentationApproximationCone.π.app J =
      e.toImage ≫ IdealSheafData.inclusion J.unop.property.1 := rfl

/-- Every component recovers the original closed immersion, not merely an isomorphic map. -/
@[reassoc (attr := simp)]
lemma finitePresentationApproximationCone_comp
    (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) :
    ((e.toImage ≫ IdealSheafData.inclusion J.unop.property.1) ≫
      e.finitePresentationApproximationStructure.app J : X ⟶ Y) = e := by
  change (e.toImage ≫ IdealSheafData.inclusion J.unop.property.1) ≫
    J.unop.val.subschemeι = e
  rw [Category.assoc, IdealSheafData.inclusion_subschemeι]
  exact e.toImage_imageι

/-- Closed-immersion transitions are retained by the underlying scheme diagram. -/
instance finitePresentationApproximation_map_isClosedImmersion
    {J K : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ} (f : J ⟶ K) :
    IsClosedImmersion (e.finitePresentationApproximationDiagram.map f) := by
  change IsClosedImmersion ((e.ker.finitePresentationApproximationDiagram).map f).left
  infer_instance

instance finitePresentationApproximation_structure_isClosedImmersion
    (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) :
    IsClosedImmersion (e.finitePresentationApproximationStructure.app J) := by
  change IsClosedImmersion J.unop.val.subschemeι
  infer_instance

instance finitePresentationApproximation_structure_locallyOfFinitePresentation
    (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) :
    LocallyOfFinitePresentation (e.finitePresentationApproximationStructure.app J) :=
  J.unop.val.locallyOfFinitePresentation_subschemeι_iff.mpr J.unop.property.2

/-- The original source is the actual limit; the only change of vertex is its
native isomorphism to the closed image, supplied by closed immersiveness. -/
def finitePresentationApproximationConeIsLimit [IsClosedImmersion e]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsLimit e.finitePresentationApproximationCone := by
  change IsLimit (e.ker.finitePresentationApproximationSchemeCone.extend e.toImage)
  exact IsLimit.extendIso (s := e.ker.finitePresentationApproximationSchemeCone)
    e.toImage e.ker.finitePresentationApproximationSchemeConeIsLimit

instance finitePresentationApproximation_cone_isClosedImmersion [IsClosedImmersion e]
    (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) :
    IsClosedImmersion (e.finitePresentationApproximationCone.π.app J) := by
  rw [finitePresentationApproximationCone_π_app]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
