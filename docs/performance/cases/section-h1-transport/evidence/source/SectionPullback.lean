/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection.Transport

/-!
# Actual section pullback on small-etale H¹

Generic A1/A5 support for `K2-018#eq:k2018-pointed-character`, frozen
engineering basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
The map uses the actual exact inverse-image functors, their canonical
composition/identity isomorphisms, and the given scheme section equation.
No torsor, fundamental-group, or cohomology-comparison premise is involved.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
universe u w w'
attribute [local instance] hasSheafifyLarge
variable {B X : Scheme.{u}} (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)

/-- The actual coefficient identification after pullback along the section.
Only the canonical inverse-image composition and identity isomorphisms occur. -/
def sectionCoefficientIso (L : AbelianSheaf.{u, u + 1} B) :
    (inverseImage o).obj ((inverseImage p).obj L) ≅ L :=
  ((inverseImageComp p o).app L).symm ≪≫
    eqToIso (congrArg (fun f : B ⟶ B => (inverseImage f).obj L) h) ≪≫
      (inverseImageId B).app L

/-- The same original coefficient comparison as a whole natural isomorphism. -/
def sectionCoefficientNatIso :
    inverseImage p ⋙ inverseImage o ≅ 𝟭 (AbelianSheaf.{u, u + 1} B) :=
  Functor.sourceSectionIso (inverseImageComp p o)
    (eqToIso (congrArg (fun f : B ⟶ B => inverseImage f) h) ≪≫ inverseImageId B)

/-- The whole coefficient comparison has exactly the original component. -/
theorem sectionCoefficientNatIso_app (L : AbelianSheaf.{u, u + 1} B) :
    (sectionCoefficientNatIso p o h).app L = sectionCoefficientIso p o h L :=
  Functor.sourceSectionIso_transport_app (fun f : B ⟶ B => inverseImage f) h
    (inverseImageComp p o) (inverseImageId B) L

/-- Named whole value equality for original section and stalk consumers. -/
theorem sectionCoefficientIso_hom_eq_original (L : AbelianSheaf.{u, u + 1} B) :
    (sectionCoefficientIso p o h L).hom =
      (inverseImageComp p o).inv.app L ≫
        eqToHom (congrArg (fun f : B ⟶ B => (inverseImage f).obj L) h) ≫
          (inverseImageId B).hom.app L := rfl

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]

/-- The actual H¹ pullback to the section, with its original coefficient sheaf. -/
def sectionPullback (L : AbelianSheaf.{u, u + 1} B) :
    H1Etale.{u, u + 1, w'} X ((inverseImage p).obj L) →+ H1Etale.{u, u + 1, w} B L :=
  (coefficientIso (sectionCoefficientIso p o h L)).toAddMonoidHom.comp
    (h1Pullback o ((inverseImage p).obj L))

/-- Equality of scheme morphisms is transported by the actual coefficient
isomorphism on inverse images, including the actual induced Ext map. -/
theorem h1Pullback_eq_transport {Y Z : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} Z)]
    {f g : Z ⟶ Y} (e : f = g) (L : AbelianSheaf.{u, u + 1} Y) (a : H1Etale Y L) :
    coefficientMap (eqToIso (congrArg (fun k : Z ⟶ Y => (inverseImage k).obj L) e)).hom
      (h1Pullback f L a) = h1Pullback g L a := by
  subst g
  change coefficientMap (𝟙 _) (h1Pullback f L a) = h1Pullback f L a
  rw [coefficientMap_id]
  rfl

/-- The actual origin pullback is a left inverse to actual base inflation. -/
theorem sectionPullback_inflation (L : AbelianSheaf.{u, u + 1} B) (a : H1Etale.{u, u + 1, w} B L) :
    sectionPullback p o h L (h1Pullback p L a) = a := by
  let T := h1Functor.{u, u + 1, w} (X := B)
  have hE : (fun b => sectionPullback p o h L b) =
      fun b => T.map (sectionCoefficientIso p o h L).hom
        (h1Pullback o ((inverseImage p).obj L) b) := rfl
  have hc := h1Pullback_comp.{u, w, w', w} p o L a
  have ht := h1Pullback_eq_transport.{u, w, w} h L a
  have he := h1Pullback_id.{u, w} B L a
  exact Functor.map_inverse_transport_apply_of_values T
    ((inverseImageComp p o).app L)
    (eqToIso (congrArg (fun f : B ⟶ B => (inverseImage f).obj L) h))
    ((inverseImageId B).app L) (sectionCoefficientIso p o h L).hom
    (sectionCoefficientIso_hom_eq_original p o h L)
    (sectionPullback p o h L) (h1Pullback o ((inverseImage p).obj L)) hE
    (h1Pullback p L a) (h1Pullback (o ≫ p) L a) (h1Pullback (𝟙 B) L a) a hc ht he

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- The canonical section coefficient isomorphism is natural for every actual
abelian coefficient-sheaf morphism, before taking cohomology. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem sectionCoefficientIso_naturality {L D : AbelianSheaf.{u, u + 1} B} (q : L ⟶ D) :
    (inverseImage o).map ((inverseImage p).map q) ≫ (sectionCoefficientIso p o h D).hom =
      (sectionCoefficientIso p o h L).hom ≫ q := by
  have hn := (sectionCoefficientNatIso p o h).hom.naturality q
  simpa only [Functor.comp_map, Functor.id_map, ← Iso.app_hom,
    sectionCoefficientNatIso_app] using hn

/-- Actual section H¹ pullback commutes with the actual base coefficient map. -/
theorem sectionPullback_coefficient {L D : AbelianSheaf.{u, u + 1} B} (q : L ⟶ D)
    (a : H1Etale.{u, u + 1, w'} X ((inverseImage p).obj L)) :
    sectionPullback p o h D (coefficientMap ((inverseImage p).map q) a) =
      coefficientMap q (sectionPullback p o h L a) := by
  let T := h1Functor.{u, u + 1, w} (X := B)
  have hEL : (fun b => sectionPullback p o h L b) =
      fun b => T.map (sectionCoefficientIso p o h L).hom
        (h1Pullback o ((inverseImage p).obj L) b) := rfl
  have hED : (fun b => sectionPullback p o h D b) =
      fun b => T.map (sectionCoefficientIso p o h D).hom
        (h1Pullback o ((inverseImage p).obj D) b) := rfl
  have hQ : (fun b => coefficientMap q b) = fun b => T.map q b := rfl
  have hp := h1Pullback_coefficientMap.{u, w', w} o ((inverseImage p).map q) a
  exact Functor.map_coefficient_square_apply_of_values T
    ((inverseImage o).map ((inverseImage p).map q)) q
    (sectionCoefficientIso p o h L).hom (sectionCoefficientIso p o h D).hom
    (sectionCoefficientIso_naturality p o h q)
    (sectionPullback p o h L) (sectionPullback p o h D)
    (h1Pullback o ((inverseImage p).obj L)) (h1Pullback o ((inverseImage p).obj D))
    (coefficientMap ((inverseImage p).map q)) (coefficientMap q) hEL hED hQ a hp

end AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 21086faaf8adb9a80422f427621f1a99c23c6fd160a2b3ec59af96f508ef292d.
Definitions, hypotheses and universes are retained modulo native names. -/
