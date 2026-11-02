/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.CategoryTheory.Abelian.Ext.CoefficientSquare

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.LocalPasting` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f39a90d6a3e5be79b046f4c2192e49eca9e1a303748ad6ca0bbae3bd2330f4f6`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
namespace AlgebraicGeometry.Scheme.EtaleCohomology.LocalPasting
universe u
attribute [local instance] hasSheafifyLarge hasExtStandard
section SheafPasting
variable {B X Y Z : Scheme.{u}}
  (p : X ⟶ B) (l : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (hgl : g ≫ l = k)
  (r : Y ⟶ B) (hl : l ≫ p = r) (s : Z ⟶ B) (hg : g ≫ r = s)
  (hk : k ≫ p = s)
  {L T : AbelianSheaf.{u, u + 1} B}

/-- The two actual inverse-image triangle paths agree for every coefficient sheaf. -/
theorem triangle_pasting :
    (inverseImage g).map (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso p
      l r
        hl T).hom ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s hg T).hom =
    (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g k hgl ((inverseImage
        p).obj T)).hom ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso p k s hk T).hom := by
  simpa only [TriangleCoherence.triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.triangle_pasting
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p l g k hgl r hl s hg
      hk

/-- Transport the original iterated curve coefficient to the affine coefficient. -/
def localCoefficientIso (alpha : L ≅ T) :
    (inverseImage l).obj ((inverseImage p).obj L) ≅ (inverseImage r).obj T :=
  (inverseImage l).mapIso ((inverseImage p).mapIso alpha) ≪≫
    AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso p l r hl T

/-- The original local conversion uses the same mapped coefficient and triangle. -/
private theorem localCoefficientIso_eq_originalData
    (alpha : L ≅ T) :
    localCoefficientIso p l r hl alpha =
      CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.localIso
        Continuity.schemeAdjunctionData p l r hl alpha := by
  simp only [localCoefficientIso,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.localIso,
    TriangleCoherence.triangleIso_eq_originalData,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op]

/-- The local coefficient conversion commutes with an arbitrary scheme triangle. -/
theorem localCoefficientIso_pasting (alpha : L ≅ T) :
    (inverseImage g).map (localCoefficientIso p l r hl alpha).hom ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s hg T).hom =
    (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g k hgl ((inverseImage
        p).obj L)).hom ≫
      (localCoefficientIso p k s hk alpha).hom := by
  simpa only [localCoefficientIso_eq_originalData,
    TriangleCoherence.triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.local_pasting
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p l g k hgl r hl s hg
      hk alpha

/-- The corresponding inverse conversion, used before native local restriction. -/
theorem localCoefficientIso_inv_pasting (alpha : L ≅ T) :
    (inverseImage g).map (localCoefficientIso p l r hl alpha).inv ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g k hgl
        ((inverseImage
          p).obj L)).hom ≫
      (localCoefficientIso p k s hk alpha).hom =
        (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s hg T).hom :=
          by
  simpa only [localCoefficientIso_eq_originalData,
    TriangleCoherence.triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.local_inv_pasting
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p l g k hgl r hl s hg
      hk alpha

/-- In H1 the converted original local restriction is the ordinary affine pullback. -/
theorem local_h1_pasting (alpha : L ≅ T)
    (a : H1Etale Y ((inverseImage r).obj T)) :
    coefficientMap (localCoefficientIso p k s hk alpha).hom
      (coefficientMap (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g
        k hgl
          ((inverseImage p).obj L)).hom
        (h1Pullback g ((inverseImage l).obj ((inverseImage p).obj L))
          (coefficientMap (localCoefficientIso p l r hl alpha).inv a))) =
    coefficientMap (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s
      hg T).hom
      (h1Pullback g ((inverseImage r).obj T) a) := by
  exact CategoryTheory.Functor.extPrecompMap_postcomp_of_comp_eq
    (inverseImage g)
    ((inverseImageConstantIso g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (localCoefficientIso p l r hl alpha).inv
    (TriangleCoherence.triangleIso l g k hgl ((inverseImage p).obj L)).hom
    (localCoefficientIso p k s hk alpha).hom
    (TriangleCoherence.triangleIso r g s hg T).hom
    (localCoefficientIso_inv_pasting p l g k hgl r hl s hg hk alpha) 1 a

end SheafPasting
section IdentityCoefficient
variable {Z : Scheme.{u}} (f : Z ⟶ Z) (hf : f = 𝟙 Z) (L : AbelianSheaf.{u, u + 1} Z)

/-- The ordinary coefficient identification for a morphism equal to the identity. -/
def identityCoefficientIso : (inverseImage f).obj L ≅ L :=
  eqToIso (congrArg (fun g : Z ⟶ Z => (inverseImage g).obj L) hf) ≪≫
    (inverseImageId Z).app L

/-- Identity pullback with its explicit coefficient equality transport. -/
theorem h1_identity_transport (a : H1Etale Z L) :
    coefficientMap (identityCoefficientIso f hf L).hom (h1Pullback f L a) = a := by
  subst f
  simpa only [identityCoefficientIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Category.id_comp, Iso.app_hom, CategoryTheory.Functor.id_obj] using h1Pullback_id Z L a

end IdentityCoefficient
section SectionCoefficient
variable {B X : Scheme.{u}} (p : X ⟶ B) (o : B ⟶ X) (ho : o ≫ p = 𝟙 B)
  {L T : AbelianSheaf.{u, u + 1} B} (alpha : L ≅ T)

/-- The original section coefficient transport is natural in the base coefficient. -/
theorem localCoefficientIso_section :
    (localCoefficientIso p o (𝟙 B) ho alpha).hom ≫ (inverseImageId B).hom.app T =
      (sectionCoefficientIso p o ho L).hom ≫ alpha.hom := by
  simpa only [localCoefficientIso,
    AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso,
    sectionCoefficientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using (sectionCoefficientIso_naturality p o ho alpha.hom)

/-- The same section-coefficient equation with a displayed affine identity map. -/
theorem localCoefficientIso_section_transport (f : B ⟶ B) (hf : f = 𝟙 B) :
    (localCoefficientIso p o f (ho.trans hf.symm) alpha).hom ≫
      (identityCoefficientIso f hf T).hom =
    (sectionCoefficientIso p o ho L).hom ≫ alpha.hom := by
  subst f
  simpa only [identityCoefficientIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Category.id_comp, Iso.app_hom, CategoryTheory.Functor.id_obj] using
        localCoefficientIso_section p o ho alpha

end SectionCoefficient
end AlgebraicGeometry.Scheme.EtaleCohomology.LocalPasting
