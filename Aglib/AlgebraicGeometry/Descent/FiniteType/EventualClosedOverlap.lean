/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.EventualAffineOverlap
public import Aglib.AlgebraicGeometry.Descent.FiniteType.OverlapGeneration
public import Aglib.AlgebraicGeometry.Descent.FiniteType.AffineClosedImmersion

/-!
# Eventual closedness of a fixed pair of relative charts

An affine overlap tail is derived from separatedness of the limit. The
actual product cone and overlap cone retain their limits on that tail.
Generation, not cartesian diagonal transitions, supplies eventual
closedness and persistence at every later stage.
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
  [∀ j, QuasiSeparatedSpace (D.obj j)]
  {S : Scheme.{u}} [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
  (c : Cone D) (hc : IsLimit c) (h : c.pt ⟶ S)
  (hcompat : ∀ j, c.π.app j ≫ t.app j = h)
  (i : I) (U V : (D.obj i).Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)

omit [IsCofiltered I] [∀ j, QuasiSeparatedSpace (D.obj j)] in
include hU hV in
/-- The actual relative product stage is affine over the fixed affine base. -/
lemma isAffine_product_obj (j : Over i) : IsAffine ((productDiagram D t i U V).obj j) := by
  have : IsAffine (D.map j.hom ⁻¹ᵁ U).toScheme := hU.preimage (D.map j.hom)
  have : IsAffineHom ((D.map j.hom ⁻¹ᵁ V).ι ≫ t.app j.left) :=
    @isAffineHom_of_isAffine (D.map j.hom ⁻¹ᵁ V).toScheme S
      ((D.map j.hom ⁻¹ᵁ V).ι ≫ t.app j.left)
      (hV.preimage (D.map j.hom)) inferInstance
  exact IsAffine.of_isPullback (IsPullback.of_hasPullback
    ((D.map j.hom ⁻¹ᵁ U).ι ≫ t.app j.left)
    ((D.map j.hom ⁻¹ᵁ V).ι ≫ t.app j.left))

omit [IsCofiltered I] [∀ j, QuasiSeparatedSpace (D.obj j)] in
include hU hV in
/-- Closedness of a particular overlap arrow persists along a transition
by ring generation and naturality, not by a cartesian product square. -/
lemma isClosedImmersion_overlapMap_of_transition {j k : Over i} (q : j ⟶ k)
    [IsClosedImmersion ((overlapMap D t i U V).app k)] :
    IsClosedImmersion ((overlapMap D t i U V).app j) := by
  have : IsAffine ((productDiagram D t i U V).obj k) :=
    isAffine_product_obj D t i U V hU hV k
  have : IsAffine ((productDiagram D t i U V).obj j) :=
    isAffine_product_obj D t i U V hU hV j
  have : IsAffine ((opensDiagram D i (U ⊓ V)).obj k) :=
    isAffine_of_isAffineHom ((overlapMap D t i U V).app k)
  have : IsAffine ((opensDiagram D i (U ⊓ V)).obj j) :=
    isAffine_of_isAffineHom ((opensDiagram D i (U ⊓ V)).map q)
  have hcomm : ((overlapMap D t i U V).app k).appTop ≫
      ((opensDiagram D i (U ⊓ V)).map q).appTop =
        ((productDiagram D t i U V).map q).appTop ≫
          ((overlapMap D t i U V).app j).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop ((overlapMap D t i U V).naturality q)
  exact IsClosedImmersion.of_surjective_of_isAffine ((overlapMap D t i U V).app j)
    (CommRingCat.surjective_of_closure_range_union_range_eq_top _ _ _ _ hcomm
      (closure_range_overlapMap_eq_top D i t U V hU q)
      (IsClosedImmersion.isAffine_surjective_of_isAffine ((overlapMap D t i U V).app k)).2)

include hc hcompat hU hV in
/-- A fixed chart pair has a closed overlap arrow at some stage, obtained
from the actual affine tail and the generation-based descent core. -/
lemma exists_isClosedImmersion_overlapMap [IsSeparated h] :
    ∃ j : Over i, IsClosedImmersion ((overlapMap D t i U V).app j) := by
  obtain ⟨j, hj⟩ := exists_isAffine_overlap_obj D t c hc h hcompat i U V hU hV
  let W := opensDiagram D i (U ⊓ V)
  let P := productDiagram D t i U V
  have : IsAffine (W.obj j) := hj
  let DS := Over.forget j ⋙ W
  let ES := Over.forget j ⋙ P
  let cW : Cone DS := (opensCone D c i (U ⊓ V)).whisker (Over.forget j)
  let cP : Cone ES := (productCone D t c h hcompat i U V).whisker (Over.forget j)
  have hW : IsLimit cW :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) (opensCone D c i (U ⊓ V))).symm
      (isLimitOpensCone D c hc i (U ⊓ V))
  have hP : IsLimit cP :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j)
      (productCone D t c h hcompat i U V)).symm
      (isLimitProductCone D t c h hcompat i U V hc)
  have (k : Over j) : IsAffine (DS.obj k) := by
    change IsAffine (W.obj k.left)
    exact isAffine_of_isAffineHom (W.map k.hom)
  have (k : Over j) : IsAffine (ES.obj k) :=
    isAffine_product_obj D t i U V hU hV k.left
  let β : DS ⟶ ES := Functor.whiskerLeft (Over.forget j) (overlapMap D t i U V)
  have hβ (k : Over j) : overlapLimitMap D t c h hcompat i U V ≫ cP.π.app k =
      cW.π.app k ≫ β.app k := overlapLimitMap_comp_π D t c h hcompat i U V k.left
  have : LocallyOfFiniteType (β.app (Over.mk (𝟙 j))) :=
    locallyOfFiniteType_overlapMap_app D t i U V j
  have : IsClosedImmersion (overlapLimitMap D t c h hcompat i U V) :=
    isClosedImmersion_overlapLimitMap D t c h hcompat i U V
  have hgenerate (k : Over j) (q : k ⟶ Over.mk (𝟙 j)) :
      Subring.closure (Set.range (DS.map q).appTop ∪ Set.range (β.app k).appTop) = ⊤ := by
    have : IsAffine ((opensDiagram D i (U ⊓ V)).obj j) := hj
    exact closure_range_overlapMap_eq_top D i t U V hU (k := j) q.left
  obtain ⟨k, _, hk⟩ := Scheme.exists_isClosedImmersion_app_of_isLimit_of_isAffine_of_closure_eq_top
    DS ES β cW hW cP hP (overlapLimitMap D t c h hcompat i U V) hβ
    (Over.mk (𝟙 j)) hgenerate
  exact ⟨k.left, hk⟩

include hc hcompat hU hV in
/-- A fixed chart pair has closed overlap arrows at some stage and every
later stage. No original source stage is assumed affine, and no
finite-presentation assumption is imposed on the diagonal. -/
lemma exists_eventually_isClosedImmersion_overlapMap [IsSeparated h] :
    ∃ j : Over i, ∀ (k : Over i) (_q : k ⟶ j),
      IsClosedImmersion ((overlapMap D t i U V).app k) := by
  obtain ⟨j, hj⟩ := exists_isClosedImmersion_overlapMap D t c hc h hcompat i U V hU hV
  have : IsClosedImmersion ((overlapMap D t i U V).app j) := hj
  exact ⟨j, fun k q ↦ isClosedImmersion_overlapMap_of_transition D t i U V hU hV q⟩

end AlgebraicGeometry.Scheme.RelativeOverlap
