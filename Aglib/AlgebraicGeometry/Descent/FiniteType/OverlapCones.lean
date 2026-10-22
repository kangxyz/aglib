/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.OverlapDiagrams

/-!
# Actual limit cones for relative chart products

The relative product of the two native chart limit schemes is shown to
limit their product diagram by its universal property. Its projections
and its compatibility with the actual overlap map are retained explicitly.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeOverlap

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
  (c : Cone D) (h : c.pt ⟶ S)
  (hcompat : ∀ j, c.π.app j ≫ t.app j = h)
  (i : I) (U V : (D.obj i).Opens)

/-- First projection of the actual product diagram. -/
def productFst : productDiagram D t i U V ⟶ opensDiagram D i U where
  app _ := pullback.fst _ _
  naturality _ _ q := productDiagram_map_fst D t i U V q

/-- Second projection of the actual product diagram. -/
def productSnd : productDiagram D t i U V ⟶ opensDiagram D i V where
  app _ := pullback.snd _ _
  naturality _ _ q := productDiagram_map_snd D t i U V q

include hcompat in
lemma chartCone_structure (j : Over i) :
    (opensCone D c i U).π.app j ≫ (chartStructure D t i U).app j =
      (c.π.app i ⁻¹ᵁ U).ι ≫ h := by
  change (c.π.app j.left).resLE _ _ _ ≫
    ((D.map j.hom ⁻¹ᵁ U).ι ≫ t.app j.left) = _
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hcompat]

/-- The product of the literal inverse-image-open limit schemes. -/
def productCone : Cone (productDiagram D t i U V) where
  pt := product h (c.π.app i ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ V)
  π.app j := pullback.map _ _ _ _
    ((opensCone D c i U).π.app j) ((opensCone D c i V).π.app j) (𝟙 S)
    (by simpa using (chartCone_structure D t c h hcompat i U j).symm)
    (by simpa using (chartCone_structure D t c h hcompat i V j).symm)
  π.naturality j k q := by
    apply pullback.hom_ext
    · simp only [Functor.const_obj_map, Category.assoc, chartStructure_app,
        productDiagram_map_fst, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
      exact congrArg (fun z ↦ pullback.fst _ _ ≫ z) ((opensCone D c i U).w q).symm
    · simp only [Functor.const_obj_map, Category.assoc, chartStructure_app,
        productDiagram_map_snd, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
      exact congrArg (fun z ↦ pullback.snd _ _ ≫ z) ((opensCone D c i V).w q).symm

@[reassoc (attr := simp)]
lemma productCone_π_fst (j : Over i) :
    ((productCone D t c h hcompat i U V).π.app j ≫
        pullback.fst (Z := S) ((D.map j.hom ⁻¹ᵁ U).ι ≫ t.app j.left)
          ((D.map j.hom ⁻¹ᵁ V).ι ≫ t.app j.left) :
      (productCone D t c h hcompat i U V).pt ⟶ (D.map j.hom ⁻¹ᵁ U).toScheme) =
      pullback.fst _ _ ≫ (opensCone D c i U).π.app j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma productCone_π_snd (j : Over i) :
    ((productCone D t c h hcompat i U V).π.app j ≫
        pullback.snd (Z := S) ((D.map j.hom ⁻¹ᵁ U).ι ≫ t.app j.left)
          ((D.map j.hom ⁻¹ᵁ V).ι ≫ t.app j.left) :
      (productCone D t c h hcompat i U V).pt ⟶ (D.map j.hom ⁻¹ᵁ V).toScheme) =
      pullback.snd _ _ ≫ (opensCone D c i V).π.app j :=
  pullback.lift_snd _ _ _

/-- The product cone is limiting by the two native chart universal properties. -/
def isLimitProductCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (productCone D t c h hcompat i U V) := by
  let hU := isLimitOpensCone D c hc i U
  let hV := isLimitOpensCone D c hc i V
  let sU (s : Cone (productDiagram D t i U V)) : Cone (opensDiagram D i U) :=
    { pt := s.pt, π := s.π ≫ productFst D t i U V }
  let sV (s : Cone (productDiagram D t i U V)) : Cone (opensDiagram D i V) :=
    { pt := s.pt, π := s.π ≫ productSnd D t i U V }
  have hcomm (s : Cone (productDiagram D t i U V)) :
      hU.lift (sU s) ≫ ((c.π.app i ⁻¹ᵁ U).ι ≫ h) =
        hV.lift (sV s) ≫ ((c.π.app i ⁻¹ᵁ V).ι ≫ h) := by
    let j : Over i := Over.mk (𝟙 i)
    rw [← chartCone_structure D t c h hcompat i U j,
      ← chartCone_structure D t c h hcompat i V j,
      ← Category.assoc, ← Category.assoc, hU.fac, hV.fac]
    change (s.π.app j ≫ pullback.fst _ _) ≫ _ =
      (s.π.app j ≫ pullback.snd _ _) ≫ _
    simp only [Category.assoc, pullback.condition]
  let l (s : Cone (productDiagram D t i U V)) :
      s.pt ⟶ (productCone D t c h hcompat i U V).pt :=
    pullback.lift (hU.lift (sU s)) (hV.lift (sV s)) (hcomm s)
  refine { lift := l, fac := ?_, uniq := ?_ }
  · intro s j
    apply pullback.hom_ext
    · simp only [Category.assoc, chartStructure_app, productCone_π_fst, l,
        pullback.lift_fst_assoc]
      exact hU.fac (sU s) j
    · simp only [Category.assoc, chartStructure_app, productCone_π_snd, l,
        pullback.lift_snd_assoc]
      exact hV.fac (sV s) j
  · intro s m hm
    apply pullback.hom_ext
    · apply hU.hom_ext
      intro j
      calc
        (m ≫ pullback.fst _ _) ≫ (opensCone D c i U).π.app j =
            (m ≫ (productCone D t c h hcompat i U V).π.app j) ≫
              pullback.fst _ _ := by
                simp only [Category.assoc, chartStructure_app, productCone_π_fst]
        _ = s.π.app j ≫ pullback.fst _ _ := by rw [hm]
        _ = (l s ≫ pullback.fst _ _) ≫ (opensCone D c i U).π.app j := by
          simp only [l, pullback.lift_fst]
          exact (hU.fac (sU s) j).symm
    · apply hV.hom_ext
      intro j
      calc
        (m ≫ pullback.snd _ _) ≫ (opensCone D c i V).π.app j =
            (m ≫ (productCone D t c h hcompat i U V).π.app j) ≫
              pullback.snd _ _ := by
                simp only [Category.assoc, chartStructure_app, productCone_π_snd]
        _ = s.π.app j ≫ pullback.snd _ _ := by rw [hm]
        _ = (l s ≫ pullback.snd _ _) ≫ (opensCone D c i V).π.app j := by
          simp only [l, pullback.lift_snd]
          exact (hV.fac (sV s) j).symm

/-- The actual overlap limit arrow. -/
def overlapLimitMap : (opensCone D c i (U ⊓ V)).pt ⟶
    (productCone D t c h hcompat i U V).pt :=
  toProduct h (c.π.app i ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ V)

/-- The overlap cone and product cone commute with the actual overlap maps. -/
lemma overlapLimitMap_comp_π (j : Over i) :
    overlapLimitMap D t c h hcompat i U V ≫
        (productCone D t c h hcompat i U V).π.app j =
      (opensCone D c i (U ⊓ V)).π.app j ≫ (overlapMap D t i U V).app j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chartStructure_app, productCone_π_fst, overlapMap,
      overlapLimitMap, toProduct_fst_assoc]
    apply (cancel_mono (D.map j.hom ⁻¹ᵁ U).ι).mp
    simp [opensCone, Scheme.Hom.resLE_comp_ι]
    rfl
  · simp only [Category.assoc, chartStructure_app, productCone_π_snd, overlapMap,
      overlapLimitMap, toProduct_snd_assoc]
    apply (cancel_mono (D.map j.hom ⁻¹ᵁ V).ι).mp
    simp [opensCone, Scheme.Hom.resLE_comp_ι]
    rfl

end AlgebraicGeometry.Scheme.RelativeOverlap
