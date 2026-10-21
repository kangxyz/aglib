/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SheafCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback

/-!
# Actual represented group and H1 base-change squares

A supplied equation between the actual group-pullback isomorphisms
gives the represented-sheaf square and its H1 square. The geometric point,
Galois-category/fibre-functor classes, finite-etale inputs and all three
Ext universes remain explicit. No generic cohomology square is an input.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.FullFaithful`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`6cc872fee4d63ecd6b0adac1742e51e1cf2e2d26efa6df80aa606caed7975589`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.SheafCoherence
open AlgebraicGeometry.Scheme.Group.BaseChange
open AlgebraicGeometry.Scheme.Group.BaseChange.PointTransport
open AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

namespace AlgebraicGeometry.Scheme.EtaleCohomology.GroupBaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory

section SheafSquare
universe wX wC wZ
variable {X C Z : Scheme.{u}} (i : C ⟶ X) (j : Z ⟶ C) (g : Z ⟶ X) (h : j ≫ i = g)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Z)
  [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite t)]
  (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
  (J : Grp (Over C)) [IsCommMonObj J.X] [Etale J.X.hom]
  (L : Grp (Over Z)) [IsCommMonObj L.X]
  (δ : (Over.pullback i).mapGrp.obj H ≅ J)
  (α : (Over.pullback j).mapGrp.obj J ≅ L)
  (β : (Over.pullback g).mapGrp.obj H ≅ L)
  (hδ : (Over.pullback j).mapGrp.map δ.hom =
    (groupPullbackCompIso j i H).hom ≫
      (eqToIso (congrArg (fun f => baseChangedGroup f H) h)).hom ≫ β.hom ≫ α.inv)

include hδ t in
theorem represented_group_generic_square :
    (inverseImageComp i j).hom.app (representedSheaf H) ≫
      (inverseImage j).map ((representedSheafBaseChangeIso i H).hom ≫ representedSheafMap δ.hom) ≫
      (representedSheafBaseChangeIso j J).hom ≫ representedSheafMap α.hom =
    (eqToIso (congrArg (fun f => (inverseImage f).obj (representedSheaf H)) h)).hom ≫
      (representedSheafBaseChangeIso g H).hom ≫ representedSheafMap β.hom := by
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (representedSheafBaseChangeIso_naturality j δ.hom), hδ]
  simp only [representedSheafMap_comp, Category.assoc]
  rw [← representedSheafMap_comp α.inv α.hom, Iso.inv_hom_id, representedSheafMap_id,
    Category.comp_id]
  rw [reassoc_of% (representedSheafBaseChangeIso_comp i j t H)]
  rw [reassoc_of% (representedSheafBaseChangeIso_congr h H)]

variable [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wC} (AbelianSheaf.{u, u + 1} C)] [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]

include hδ t in
theorem represented_group_generic_h1_square
    (a : H1Etale.{u, u + 1, wX} X (representedSheaf H)) :
    coefficientMap.{u, u + 1, wZ}
      ((representedSheafBaseChangeIso j J).hom ≫ representedSheafMap α.hom)
      (h1Pullback.{u, wC, wZ} j (representedSheaf J)
        (coefficientMap.{u, u + 1, wC}
          ((representedSheafBaseChangeIso i H).hom ≫ representedSheafMap δ.hom)
          (h1Pullback.{u, wX, wC} i (representedSheaf H) a))) =
    coefficientMap.{u, u + 1, wZ}
      ((representedSheafBaseChangeIso g H).hom ≫ representedSheafMap β.hom)
      (h1Pullback.{u, wX, wZ} g (representedSheaf H) a) := by
  have hcomp {P Q R : AbelianSheaf.{u, u + 1} Z} (q : P ⟶ Q) (r : Q ⟶ R)
      (b : H1Etale.{u, u + 1, wZ} Z P) :
      coefficientMap.{u, u + 1, wZ} r (coefficientMap.{u, u + 1, wZ} q b) =
        coefficientMap.{u, u + 1, wZ} (q ≫ r) b :=
    (congrArg (fun f : H1Etale.{u, u + 1, wZ} Z P →+ H1Etale.{u, u + 1, wZ} Z R => f b)
      (coefficientMap_comp.{u, u + 1, wZ} (X := Z) q r)).symm
  rw [h1Pullback_coefficientMap, ← h1Pullback_comp]
  rw [hcomp]
  have hh := hcomp ((inverseImageComp i j).hom.app (representedSheaf H))
    ((inverseImage j).map
        ((representedSheafBaseChangeIso i H).hom ≫ representedSheafMap δ.hom) ≫
      (representedSheafBaseChangeIso j J).hom ≫ representedSheafMap α.hom)
    (h1Pullback.{u, wX, wZ} (j ≫ i) (representedSheaf H) a)
  refine hh.trans ?_
  rw [represented_group_generic_square i j g h t H J L δ α β hδ]
  rw [← hcomp, PointedNaturality.h1Pullback_eq_transport h]

end SheafSquare

end AlgebraicGeometry.Scheme.EtaleCohomology.GroupBaseChange
