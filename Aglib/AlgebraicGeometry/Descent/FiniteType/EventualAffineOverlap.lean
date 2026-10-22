/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.OverlapCones

/-!
# Eventual affineness of an overlap over an affine fixed base

Separatedness of the limit structural morphism makes the actual overlap
limit arrow closed. Its product-chart target is affine, so the overlap
limit is affine. Affine-transition descent then gives an affine overlap
at a genuine stage of the native `Over i` system.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeOverlap

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
  {S : Scheme.{u}} [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
  (c : Cone D) (hc : IsLimit c) (h : c.pt ⟶ S)
  (hcompat : ∀ j, c.π.app j ≫ t.app j = h)
  (i : I) (U V : (D.obj i).Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)

omit [IsCofiltered I] in
include hU in
/-- Every inverse-image affine chart remains affine under the original
transition morphism; the source stages themselves need not be affine. -/
lemma isAffine_chart_obj (j : Over i) : IsAffine ((opensDiagram D i U).obj j) :=
  hU.preimage (D.map j.hom)

omit [IsCofiltered I] in
include hU hV in
/-- Overlap stages are compact as intersections of two affine opens in a
quasi-separated stage. -/
lemma compactSpace_overlap_obj [∀ j, QuasiSeparatedSpace (D.obj j)] (j : Over i) :
    CompactSpace ((opensDiagram D i (U ⊓ V)).obj j) := by
  apply isCompact_iff_compactSpace.mp
  exact QuasiSeparatedSpace.inter_isCompact _ _
    (D.map j.hom ⁻¹ᵁ U).isOpen (hU.preimage (D.map j.hom)).isCompact
    (D.map j.hom ⁻¹ᵁ V).isOpen (hV.preimage (D.map j.hom)).isCompact

omit [IsCofiltered I] [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)] in
/-- Open overlap stages inherit quasi-separatedness from the stage. -/
lemma quasiSeparatedSpace_overlap_obj [∀ j, QuasiSeparatedSpace (D.obj j)] (j : Over i) :
    QuasiSeparatedSpace ((opensDiagram D i (U ⊓ V)).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ (U ⊓ V)).isOpen).mp
    (.of_quasiSeparatedSpace _)

include hc hU hV in
/-- The product of the actual affine chart limits is affine over the affine base. -/
lemma isAffine_productCone : IsAffine (productCone D t c h hcompat i U V).pt := by
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  have : IsAffine (c.π.app i ⁻¹ᵁ U).toScheme := hU.preimage (c.π.app i)
  have : IsAffine (c.π.app i ⁻¹ᵁ V).toScheme := hV.preimage (c.π.app i)
  dsimp [productCone, product]
  infer_instance

omit [IsCofiltered I] [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)] [IsAffine S] in
/-- The literal overlap limit arrow is closed when the limit map to the
fixed base is separated. -/
lemma isClosedImmersion_overlapLimitMap [IsSeparated h] :
    IsClosedImmersion (overlapLimitMap D t c h hcompat i U V) :=
  isClosedImmersion_toProduct h _ _

include hc hU hV hcompat in
/-- Eventual affineness of the overlap uses the actual overlap limit and
native affine-transition descent, not cartesian diagonal transitions. -/
lemma exists_isAffine_overlap_obj [∀ j, QuasiSeparatedSpace (D.obj j)] [IsSeparated h] :
    ∃ j : Over i, IsAffine ((opensDiagram D i (U ⊓ V)).obj j) := by
  have (j : Over i) : CompactSpace ((opensDiagram D i (U ⊓ V)).obj j) :=
    compactSpace_overlap_obj D i U V hU hV j
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i (U ⊓ V)).obj j) :=
    quasiSeparatedSpace_overlap_obj D i U V j
  have := isAffine_productCone D t c hc h hcompat i U V hU hV
  have := isClosedImmersion_overlapLimitMap D t c h hcompat i U V
  have : IsAffine (opensCone D c i (U ⊓ V)).pt :=
    isAffine_of_isAffineHom (overlapLimitMap D t c h hcompat i U V)
  exact Scheme.exists_isAffine_of_isLimit (opensDiagram D i (U ⊓ V))
    (opensCone D c i (U ⊓ V)) (isLimitOpensCone D c hc i (U ⊓ V))

end AlgebraicGeometry.Scheme.RelativeOverlap
