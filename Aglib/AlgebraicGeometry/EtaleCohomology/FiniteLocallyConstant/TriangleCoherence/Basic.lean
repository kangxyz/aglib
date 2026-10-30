/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients
public import
  Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.OrdinaryTrianglePasting

/-!
# Ordinary inverse-image coefficient triangles

The pure ordinary laws of `FiniteLocallyConstant.TriangleCoherence` are retained here
with its original public names, statements, literal triangle value and proofs.
The canonical composition map is the component of the same original
`Continuity.schemeAdjunctionData`; the generic pasting proof is unchanged.
Arithmetic, roots and function-field applications remain in the parent module.

Original migration source:
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.TriangleCoherence`
at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f2856da541624b0c9ba45549715dcc43057aa759c5d25d05cd66860e80301f96`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence

universe u w w' w'' w'''

/-- Evaluation form of coefficient functoriality, avoiding partial-hom rewriting. -/
theorem coefficientMap_comp_apply {Y : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    {L M N : AbelianSheaf.{u, u + 1} Y} (q : L ⟶ M) (r : M ⟶ N) (a : H1Etale Y L) :
    coefficientMap r (coefficientMap q a) = coefficientMap (q ≫ r) a :=
  (congrArg (fun h : H1Etale Y L →+ H1Etale Y N => h a) (coefficientMap_comp q r)).symm

/-- Pure categorical cancellation, keeping all later scheme endpoints opaque. -/
theorem iso_cancel_right_pair {V : Type*} [Category V] {A B C D E : V}
    (a : A ≅ B) (b : B ⟶ C) (c : D ≅ C) (d : E ≅ D) (e : A ⟶ E)
    (h : a.hom ≫ b = e ≫ d.hom ≫ c.hom) :
    b ≫ c.inv ≫ d.inv = a.inv ≫ e := by
  exact CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.cancel_right_pair a b c d e h

/-- A second pure categorical cancellation for inverse triangle pasting. -/
theorem iso_factor_inverse {V : Type*} [Category V] {X Y Z T : V}
    (a : X ⟶ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : X ≅ T)
    (h : a ≫ b.hom ≫ c.hom = d.hom) :
    c.inv ≫ b.inv = d.inv ≫ a := by
  exact CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.factor_inverse a b c d h

/-- The literal inverse-image coefficient transport along a scheme triangle. -/
def triangleIso {B X Y : Scheme.{u}} (p : X ⟶ B) (f : Y ⟶ X)
    (q : Y ⟶ B) (hf : f ≫ p = q) (L : AbelianSheaf.{u, u + 1} B) :
    (inverseImage f).obj ((inverseImage p).obj L) ≅ (inverseImage q).obj L :=
  ((inverseImageComp p f).app L).symm ≪≫
    eqToIso (congrArg (fun k => (inverseImage k).obj L) hf)

/-- The original literal triangle is the inverse component of the one native
adjunction-data comparison. Its composition map is identified by its actual mate. -/
theorem triangleIso_eq_originalData {B X Y : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (q : Y ⟶ B) (hf : f ≫ p = q)
    (L : AbelianSheaf.{u, u + 1} B) :
    triangleIso p f q hf L =
      CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.iso
        Continuity.schemeAdjunctionData p f q hf L := by
  rw [CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.iso_eq_composition]
  dsimp only [CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull]
  rw [Continuity.schemeLeftCompIso_eq_inverseImageComp]
  rfl

/-- Coherence of the actual triangle transport is proved before using Ext. -/
theorem triangleIso_comp {B X Y Z : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : AbelianSheaf.{u, u + 1} B} :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
        (inverseImage g).map (triangleIso p f q hf L).hom ≫
        (triangleIso q g r hg L).hom =
      (triangleIso p (g ≫ f) r
        ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.comp
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p f g q hf r hg (L :=
      L)

/-- The same coherence with the final triangle moved to the other side. -/
theorem triangleIso_comp_inv {B X Y Z : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : AbelianSheaf.{u, u + 1} B} :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
        (inverseImage g).map (triangleIso p f q hf L).hom =
      (triangleIso p (g ≫ f) r
        ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
        (triangleIso q g r hg L).inv := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.comp_inv
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p f g q hf r hg (L :=
      L)

/-- Equality of actual generic maps gives precisely the corresponding transport. -/
theorem triangleIso_congr {B X Y : Scheme.{u}} (p : X ⟶ B)
    {f g : Y ⟶ X} (e : f = g) (q : Y ⟶ B) (hf : f ≫ p = q) (hg : g ≫ p = q)
    (L : AbelianSheaf.{u, u + 1} B) :
    (eqToIso (congrArg (fun k => (inverseImage k).obj ((inverseImage p).obj L)) e)).hom ≫
        (triangleIso p g q hg L).hom = (triangleIso p f q hf L).hom := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.congr
      Continuity.schemeAdjunctionData p e q hf hg L

/-- Inverse-image composition is natural in the literal coefficient map. -/
theorem inverseImageComp_map {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {L M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) :
    (inverseImageComp f g).hom.app L ≫ (inverseImage g).map ((inverseImage f).map q) =
      (inverseImage (g ≫ f)).map q ≫ (inverseImageComp f g).hom.app M :=
  ((inverseImageComp f g).hom.naturality q).symm

section CoefficientPasting
variable {B X Y Z : Scheme.{u}}

/-- Inverse triangle transport reassociates with actual inverse-image composition. -/
theorem triangleIso_assoc_inv (b : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (r : Z ⟶ B) (h : g ≫ (f ≫ b) = r)
    {L : AbelianSheaf.{u, u + 1} B} :
    (triangleIso (f ≫ b) g r h L).inv ≫
      (inverseImage g).map ((inverseImageComp b f).hom.app L) =
    (triangleIso b (g ≫ f) r ((Category.assoc g f b).trans h) L).inv ≫
      (inverseImageComp f g).hom.app ((inverseImage b).obj L) := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.assoc_inv
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent b f g r h (L := L)

/-- Inverse triangle transport respects an actual equality of generic maps. -/
theorem triangleIso_congr_inv (p : X ⟶ B) {f g : Z ⟶ X}
    (e : f = g)
    (r : Z ⟶ B) (hf : f ≫ p = r) (hg : g ≫ p = r) (L : AbelianSheaf.{u, u + 1} B) :
    (triangleIso p f r hf L).inv = (triangleIso p g r hg L).inv ≫
      (eqToIso (congrArg (fun k => (inverseImage k).obj ((inverseImage p).obj L)) e)).inv := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.congr_inv
      Continuity.schemeAdjunctionData p e r hf hg L

/-- The inverse triangle formula is kept opaque before native specialization. -/
theorem triangleIso_inv {B X Y : Scheme.{u}} (p : X ⟶ B) (f : Y ⟶ X)
    (q : Y ⟶ B) (hf : f ≫ p = q) (L : AbelianSheaf.{u, u + 1} B) :
    (triangleIso p f q hf L).inv =
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hf)).inv ≫
        (inverseImageComp p f).hom.app L := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.inv_formula
      Continuity.schemeAdjunctionData p f q hf L

/-- Pasting a triangle with arbitrary ordinary coefficient morphisms. -/
theorem triangleIso_route (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : AbelianSheaf.{u, u + 1} B}
    {N : AbelianSheaf.{u, u + 1} Y} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage q).obj L ⟶ N) (s : (inverseImage g).obj N ⟶ Q) :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
      (inverseImage g).map ((triangleIso p f q hf L).hom ≫ e) ≫ s =
    (triangleIso p (g ≫ f) r
      ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
      (triangleIso q g r hg L).inv ≫ (inverseImage g).map e ≫ s := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.route
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p f g q hf r hg e s

/-- Explicit direct-source form of the generic coefficient route. -/
theorem triangleIso_route_explicit (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : AbelianSheaf.{u, u + 1} B}
    {N : AbelianSheaf.{u, u + 1} Y} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage q).obj L ⟶ N) (s : (inverseImage g).obj N ⟶ Q) :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
      (inverseImage g).map ((triangleIso p f q hf L).hom ≫ e) ≫ s =
    (triangleIso p (g ≫ f) r
      ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hg)).inv ≫
      (inverseImageComp q g).hom.app L ≫ (inverseImage g).map e ≫ s := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.route_explicit
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p f g q hf r hg e s

end CoefficientPasting

/-- The actual scheme-triangle transport is natural in ordinary coefficient maps. -/
theorem triangleIso_naturality {B X Y : Scheme.{u}} (p : X ⟶ B) (f : Y ⟶ X)
    (r : Y ⟶ B) (hf : f ≫ p = r) {L N : AbelianSheaf.{u, u + 1} B} (q : L ⟶ N) :
    (inverseImage f).map ((inverseImage p).map q) ≫ (triangleIso p f r hf N).hom =
      (triangleIso p f r hf L).hom ≫ (inverseImage r).map q := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.naturality
      Continuity.schemeAdjunctionData p f r hf q

/-- Generic naturality of the entire geometric coefficient route, with all
ordinary coefficient sheaves kept abstract. -/
theorem geometric_coefficient_route_naturality {B C X Y : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (b : C ⟶ B) (g : Y ⟶ C) (hf : f ≫ p = g ≫ b)
    {L N : AbelianSheaf.{u, u + 1} B} {M : AbelianSheaf.{u, u + 1} C}
    {Q : AbelianSheaf.{u, u + 1} Y} (a : L ⟶ N)
    (e : (inverseImage b).obj N ⟶ M) (r : (inverseImage g).obj M ⟶ Q) :
    (inverseImage f).map ((inverseImage p).map a) ≫
      (triangleIso p f (g ≫ b) hf N).hom ≫ (inverseImageComp b g).hom.app N ≫
      (inverseImage g).map e ≫ r =
    (triangleIso p f (g ≫ b) hf L).hom ≫ (inverseImageComp b g).hom.app L ≫
      (inverseImage g).map ((inverseImage b).map a ≫ e) ≫ r := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.coefficient_route_naturality
      Continuity.schemeAdjunctionData p f b g hf a e r

/-- Iso-form of the abstract geometric coefficient route. Its two iso
parenthesizations match the native tensor and represented arithmetic definitions. -/
theorem geometric_coefficient_route_iso {B C X Y : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (b : C ⟶ B) (g : Y ⟶ C) (hf : f ≫ p = g ≫ b)
    {L N : AbelianSheaf.{u, u + 1} B} {M : AbelianSheaf.{u, u + 1} C}
    {Q : AbelianSheaf.{u, u + 1} Y} (a : L ≅ N)
    (e : (inverseImage b).obj N ≅ M) (r : (inverseImage g).obj M ≅ Q) :
    ((inverseImage f).mapIso ((inverseImage p).mapIso a)).hom ≫
      (triangleIso p f (g ≫ b) hf N ≪≫ (inverseImageComp b g).app N ≪≫
        (inverseImage g).mapIso e ≪≫ r).hom =
    (((inverseImageComp p f).app L).symm ≪≫
      eqToIso (congrArg (fun t => (inverseImage t).obj L) hf) ≪≫
      (inverseImageComp b g).app L ≪≫
      (inverseImage g).mapIso ((inverseImage b).mapIso a ≪≫ e) ≪≫ r).hom := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.coefficient_route_iso
      Continuity.schemeAdjunctionData p f b g hf a e r

/-- An ordinary common-source coefficient equation identifies the two actual
triangle restriction routes; every coefficient object remains abstract. -/
theorem triangle_coefficient_transport_eq {B X Y : Scheme.{u}}
    (p : X ⟶ B) (k : Y ⟶ X) (q : Y ⟶ B) (hk : k ≫ p = q)
    {L N : AbelianSheaf.{u, u + 1} B} {D : AbelianSheaf.{u, u + 1} X}
    {Q : AbelianSheaf.{u, u + 1} Y} (α : L ⟶ N)
    (c : (inverseImage p).obj L ⟶ D) (r : (inverseImage k).obj D ⟶ Q)
    (s : (inverseImage q).obj N ⟶ Q)
    (he : (inverseImageComp p k).hom.app L ≫ (inverseImage k).map c ≫ r =
      (eqToIso (congrArg (fun f => (inverseImage f).obj L) hk)).hom ≫
        (inverseImage q).map α ≫ s) :
    (inverseImage k).map ((inverseImage p).map α) ≫
      (triangleIso p k q hk N).hom ≫ s = (inverseImage k).map c ≫ r := by
  simpa only [triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.coefficient_transport_eq
      Continuity.schemeAdjunctionData p k q hk α c r s he

end AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence
