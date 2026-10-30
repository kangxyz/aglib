/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence.Basic
public import Aglib.CategoryTheory.Functor.CoefficientSquare

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.CoefficientSquare` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b39efd7022fab8e8451cf788b1c52dc28680e812a1004b3f4e625e1a89146685`.
Original objects, maps and universes are retained. Pure coherence omits
unused geometric comparison hypotheses.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

/-!
# Actual native coefficient pasting at the generic-point square

K2-018 arithmetic-character/generic-function-field comparison, source
 e73d98b1b5c1e5abcdebf7d058e436d792b87982, expose SHA256
 e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
The ordinary sheaf square is proved from inverse-image coherence and the
proved literal native tensor composition, prior to any Ext class.
-/
noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence
namespace AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientSquare
universe u w w' w''
attribute [local instance] hasSheafifyLarge

section Coherence
variable {B X Y Z : Scheme.{u}}

/-- Composition followed by a triangle has exactly its equality transport. -/
theorem comp_triangle_hom
    (g : Y ⟶ X) (m : Z ⟶ Y) (r : Z ⟶ X)
    (hm : m ≫ g = r) (L : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp g m).hom.app L ≫ (triangleIso g m r hm L).hom =
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hm)).hom := by
  simpa only [TriangleCoherence.triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.comp_iso_hom
      Continuity.schemeAdjunctionData g m r hm L

/-- The inner part of a pulled-back coefficient square, for arbitrary ordinary maps. -/
theorem coefficient_route_inner (b : X ⟶ B) (g : Y ⟶ X) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B}
    {N : AbelianSheaf.{u, u + 1} X} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage b).obj L ⟶ N) (d : (inverseImage r).obj N ⟶ Q) :
    (triangleIso (g ≫ b) m q
      ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)) L).inv ≫
      (inverseImage m).map ((inverseImageComp b g).hom.app L ≫ (inverseImage g).map e) ≫
      (triangleIso g m r hm N).hom ≫ d =
    (triangleIso b r q hq L).inv ≫ (inverseImage r).map e ≫ d := by
  simpa only [TriangleCoherence.triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.coefficient_route_inner
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent b g m r hm q hq e d

/-- Pasting the actual curve coefficient square with an actual generic-point triangle. -/
theorem coefficient_square_route {U : Scheme.{u}} (p : U ⟶ B) (f : Y ⟶ U)
    (b : X ⟶ B) (g : Y ⟶ X) (hf : f ≫ p = g ≫ b) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B}
    {N : AbelianSheaf.{u, u + 1} X} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage b).obj L ⟶ N) (d : (inverseImage r).obj N ⟶ Q) :
    (inverseImageComp f m).hom.app ((inverseImage p).obj L) ≫
      (inverseImage m).map ((triangleIso p f (g ≫ b) hf L).hom ≫
        (inverseImageComp b g).hom.app L ≫ (inverseImage g).map e) ≫
      (triangleIso g m r hm N).hom ≫ d =
    (triangleIso p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans
        ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)))) L).hom ≫
      (triangleIso b r q hq L).inv ≫ (inverseImage r).map e ≫ d := by
  simpa only [TriangleCoherence.triangleIso_eq_originalData,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.pull,
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.composition,
    Continuity.schemeLeftCompIso_eq_inverseImageComp,
    Continuity.schemeLeft_eq_inverseImage, Quiver.Hom.unop_op] using
    CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle.coefficient_square_route
      Continuity.schemeAdjunctionData Continuity.schemeAdjunctionData_coherent p f b g hf m r hm q
      hq e d

end Coherence


section CohomologySquare
universe wA wB wC wD
variable {X Y U V : Scheme.{u}}
variable [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] [HasExt.{wB} (AbelianSheaf.{u, u + 1} Y)]
variable [HasExt.{wC} (AbelianSheaf.{u, u + 1} U)] [HasExt.{wD} (AbelianSheaf.{u, u + 1} V)]

/-- Ext functoriality for a proved ordinary coefficient square. The supplied
coefficient equation identifies the two original pullback routes. -/
theorem h1_square_of_coefficient (f : Y ⟶ X) (m : V ⟶ Y) (k : U ⟶ X) (v : V ⟶ U)
    (hs : m ≫ f = v ≫ k) (A : AbelianSheaf.{u, u + 1} X) (B : AbelianSheaf.{u, u + 1} Y)
    (C : AbelianSheaf.{u, u + 1} U) (D : AbelianSheaf.{u, u + 1} V)
    (α : (inverseImage f).obj A ⟶ B) (β : (inverseImage m).obj B ⟶ D)
    (γ : (inverseImage k).obj A ⟶ C) (δ : (inverseImage v).obj C ⟶ D)
    (hc : (inverseImageComp f m).hom.app A ≫ (inverseImage m).map α ≫ β =
      (eqToIso (congrArg (fun t => (inverseImage t).obj A) hs)).hom ≫
        (inverseImageComp k v).hom.app A ≫ (inverseImage v).map γ ≫ δ)
    (a : H1Etale.{u, u + 1, wA} X A) :
    coefficientMap β (h1Pullback m B (coefficientMap α (h1Pullback f A a))) =
      coefficientMap δ (h1Pullback v C (coefficientMap γ (h1Pullback k A a))) := by
  let T := h1Functor.{u, u + 1, wD} (X := V)
  have hfm := h1Pullback_comp.{u, wA, wB, wD} f m A a
  have hkv := h1Pullback_comp.{u, wA, wC, wD} k v A a
  have hα := h1Pullback_coefficientMap.{u, wB, wD} m α
    (h1Pullback.{u, wA, wB} f A a)
  have hγ := h1Pullback_coefficientMap.{u, wC, wD} v γ
    (h1Pullback.{u, wA, wC} k A a)
  exact Functor.map_coefficient_square_of_family_values T
    (fun t : V ⟶ X => (inverseImage t).obj A)
    (fun t : V ⟶ X => h1Pullback.{u, wA, wD} t A a) hs
    ((inverseImageComp f m).hom.app A) ((inverseImageComp k v).hom.app A)
    ((inverseImage m).map α) β ((inverseImage v).map γ) δ hc hfm hkv hα hγ

end CohomologySquare

end AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientSquare
