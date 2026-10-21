/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback

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
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
namespace AlgebraicGeometry.Scheme.EtaleCohomology.LocalPasting
universe u
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge hasExtStandard
section SheafPasting
variable {B X Y Z : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
  (p : X ⟶ B) (l : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (hgl : g ≫ l = k)
  (r : Y ⟶ B) (hl : l ≫ p = r) (s : Z ⟶ B) (hg : g ≫ r = s)
  (hk : k ≫ p = s) (z : Spec (.of D) ⟶ Z)
  [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]
  {L T : AbelianSheaf.{u, u + 1} B} (RT : CoefficientRepresentation T)

include z RT in
/-- The two actual inverse-image triangle paths agree for a represented finite coefficient. -/
theorem triangle_pasting :
    (inverseImage g).map (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso p
      l r
        hl T).hom ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s hg T).hom =
    (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g k hgl ((inverseImage
        p).obj T)).hom ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso p k s hk T).hom := by
  apply (cancel_epi ((inverseImageComp l g).hom.app ((inverseImage p).obj T))).mp
  rw [AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso_comp p l g r hl s hg
    z RT]
  have ht := AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso_congr p hgl s
    ((Category.assoc g l p).trans ((congrArg (fun a => g ≫ a) hl).trans hg)) hk T
  simpa only [AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso, Iso.trans_hom,
      Iso.symm_hom,
    Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc] using ht.symm

/-- Transport the original iterated curve coefficient to the affine coefficient. -/
def localCoefficientIso (alpha : L ≅ T) :
    (inverseImage l).obj ((inverseImage p).obj L) ≅ (inverseImage r).obj T :=
  (inverseImage l).mapIso ((inverseImage p).mapIso alpha) ≪≫
    AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso p l r hl T

include z RT in
/-- The local coefficient conversion commutes with an arbitrary field-point triangle. -/
theorem localCoefficientIso_pasting (alpha : L ≅ T) :
    (inverseImage g).map (localCoefficientIso p l r hl alpha).hom ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s hg T).hom =
    (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g k hgl ((inverseImage
        p).obj L)).hom ≫
      (localCoefficientIso p k s hk alpha).hom := by
  simp only [localCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [triangle_pasting p l g k hgl r hl s hg hk z RT]
  rw [reassoc_of%
    (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso_naturality l
      g k hgl
    ((inverseImage p).map alpha.hom))]

include z RT in
/-- The corresponding inverse conversion, used before native local restriction. -/
theorem localCoefficientIso_inv_pasting (alpha : L ≅ T) :
    (inverseImage g).map (localCoefficientIso p l r hl alpha).inv ≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso l g k hgl
        ((inverseImage
          p).obj L)).hom ≫
      (localCoefficientIso p k s hk alpha).hom =
        (AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.triangleIso r g s hg T).hom :=
          by
  rw [← localCoefficientIso_pasting p l g k hgl r hl s hg hk z RT alpha]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

include z RT in
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
  rw [h1Pullback_coefficientMap]
  rw [AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.coefficientMap_comp_apply,
    AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence.coefficientMap_comp_apply]
  rw [localCoefficientIso_inv_pasting p l g k hgl r hl s hg hk z RT alpha]

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
