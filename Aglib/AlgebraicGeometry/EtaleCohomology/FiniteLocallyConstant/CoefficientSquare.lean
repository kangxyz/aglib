/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.CoefficientSquare` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b39efd7022fab8e8451cf788b1c52dc28680e812a1004b3f4e625e1a89146685`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.AlgebraicGeometry.Scheme.Group.BaseChange (scalarExtensionMap)
open _root_.AlgebraicGeometry.Scheme.OverField (Base)

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
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj
open AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.SheafCoherence
open AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence
namespace AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientSquare
universe u w w' w''
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

section Coherence
variable {B X Y Z : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
variable (z : Spec (.of D) ⟶ Z)
variable [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]

omit [GaloisCategory (Scheme.FiniteEtale Z)] in
/-- Composition followed by a triangle has exactly its equality transport. -/
-- Retain the original Galois-category input on the triangle source.
@[nolint unusedArguments]
theorem comp_triangle_hom [GaloisCategory (Scheme.FiniteEtale Z)]
    (g : Y ⟶ X) (m : Z ⟶ Y) (r : Z ⟶ X)
    (hm : m ≫ g = r) (L : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp g m).hom.app L ≫ (triangleIso g m r hm L).hom =
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hm)).hom := by
  simp only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.hom_inv_id_app_assoc]

include z in
/-- The inner part of a pulled-back coefficient square, for arbitrary ordinary maps. -/
theorem coefficient_route_inner (b : X ⟶ B) (g : Y ⟶ X) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
    {N : AbelianSheaf.{u, u + 1} X} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage b).obj L ⟶ N) (d : (inverseImage r).obj N ⟶ Q) :
    (triangleIso (g ≫ b) m q
      ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)) L).inv ≫
      (inverseImage m).map ((inverseImageComp b g).hom.app L ≫ (inverseImage g).map e) ≫
      (triangleIso g m r hm N).hom ≫ d =
    (triangleIso b r q hq L).inv ≫ (inverseImage r).map e ≫ d := by
  let hb : m ≫ (g ≫ b) = q := (Category.assoc m g b).symm.trans
    ((congrArg (fun t => t ≫ b) hm).trans hq)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (triangleIso_naturality g m r hm e)]
  rw [reassoc_of% (triangleIso_assoc_inv z b g m q hb (L := L) R)]
  rw [triangleIso_congr_inv b hm q _ hq L]
  simp only [Category.assoc]
  rw [reassoc_of% (comp_triangle_hom g m r hm ((inverseImage b).obj L))]
  simp only [Iso.inv_hom_id_assoc]

include z in
/-- Pasting the actual curve coefficient square with an actual generic-point triangle. -/
theorem coefficient_square_route {U : Scheme.{u}} (p : U ⟶ B) (f : Y ⟶ U)
    (b : X ⟶ B) (g : Y ⟶ X) (hf : f ≫ p = g ≫ b) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
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
  let hb : m ≫ (g ≫ b) = q := (Category.assoc m g b).symm.trans
    ((congrArg (fun t => t ≫ b) hm).trans hq)
  have ho := triangleIso_route z p f m (g ≫ b) hf q hb (L := L) R
    ((inverseImageComp b g).hom.app L ≫ (inverseImage g).map e)
    ((triangleIso g m r hm N).hom ≫ d)
  have hi := coefficient_route_inner z b g m r hm q hq R e d
  have ht := congrArg (fun t =>
    (triangleIso p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans hb)) L).hom ≫ t) hi
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using ho.trans ht
end Coherence


section CohomologySquare
universe wA wB wC wD
variable {X Y U V : Scheme.{u}}
variable [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] [HasExt.{wB} (AbelianSheaf.{u, u + 1} Y)]
variable [HasExt.{wC} (AbelianSheaf.{u, u + 1} U)] [HasExt.{wD} (AbelianSheaf.{u, u + 1} V)]

/-- Ext functoriality for a proved ordinary coefficient square. In the native
application below, the entire coefficient equation is discharged explicitly. -/
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
  rw [h1Pullback_coefficientMap, h1Pullback_coefficientMap,
    ← h1Pullback_comp f m A a, ← h1Pullback_comp k v A a]
  change Sheaf.H.map β 1 (Sheaf.H.map ((inverseImage m).map α) 1
      (Sheaf.H.map ((inverseImageComp f m).hom.app A) 1 (h1Pullback (m ≫ f) A a))) =
    Sheaf.H.map δ 1 (Sheaf.H.map ((inverseImage v).map γ) 1
      (Sheaf.H.map ((inverseImageComp k v).hom.app A) 1 (h1Pullback (v ≫ k) A a)))
  simp only [← Sheaf.H.map_comp_apply]
  calc
    _ = coefficientMap ((inverseImageComp f m).hom.app A ≫ ((inverseImage m).map α ≫ β))
        (h1Pullback (m ≫ f) A a) :=
      (Sheaf.H.map_comp_apply ((inverseImageComp f m).hom.app A)
        ((inverseImage m).map α ≫ β) (h1Pullback (m ≫ f) A a)).symm
    _ = coefficientMap ((eqToIso (congrArg (fun t => (inverseImage t).obj A) hs)).hom ≫
        (inverseImageComp k v).hom.app A ≫ (inverseImage v).map γ ≫ δ)
        (h1Pullback (m ≫ f) A a) :=
      congrArg (fun t => coefficientMap t (h1Pullback (m ≫ f) A a)) hc
    _ = coefficientMap ((inverseImageComp k v).hom.app A ≫ ((inverseImage v).map γ ≫ δ))
        (h1Pullback (v ≫ k) A a) := by
      rw [coefficientMap_comp]
      exact congrArg (coefficientMap ((inverseImageComp k v).hom.app A ≫ (inverseImage v).map γ
          ≫ δ))
        (Scheme.EtaleCohomology.PointedNaturality.h1Pullback_eq_transport hs A a)
    _ = _ := Sheaf.H.map_comp_apply ((inverseImageComp k v).hom.app A)
        ((inverseImage v).map γ ≫ δ) (h1Pullback (v ≫ k) A a)
end CohomologySquare

end AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientSquare
