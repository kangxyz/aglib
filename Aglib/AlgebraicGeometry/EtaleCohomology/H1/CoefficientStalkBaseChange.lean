/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Naturality

/-!
# Canonical stalk pullback for finite coefficient sheaves

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The canonical map on stalks is
constructed on actual germs through the actual inverse-image adjunction unit.
Its description through finite coefficient representatives is proved rather
than supplied as compatibility data.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientStalkBaseChange
open SchemeTorsorBaseChange
universe u
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian hasSheafifyLarge
variable {X S : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)

variable (L : AbelianSheaf.{u, u + 1} X)

section Represented
variable (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom]

/-- The actual coefficient-point pullback, with the sheaf-value universe lift explicit. -/
def representedPointPullback :
    AddCommGrpCat.of (RepresentedSections H (Over.mk (s ≫ f))) ⟶
      AddCommGrpCat.of (RepresentedSections (baseChangedGroup f H) (Over.mk s)) :=
  AddCommGrpCat.ofHom ((AddEquiv.ulift.trans
    (pullbackFiberMulEquiv f s H).toAdditive).trans AddEquiv.ulift.symm).toAddMonoidHom

/-- On represented coefficients the genuine unit-on-germs map is exactly
pullback of actual coefficient points, under the fixed represented sheaf iso. -/
theorem represented_stalkUnit :
    stalkUnit f s (representedSheaf H) ≫
        ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          (representedSheafBaseChangeIso f H).hom ≫
        representedFiberEvaluation s (baseChangedGroup f H) =
      representedFiberEvaluation (s ≫ f) H ≫ representedPointPullback f s H := by
  apply (Scheme.pointSmallEtale (s ≫ f)).presheafFiber_hom_ext
  intro U p
  erw [germ_stalkUnit_assoc]
  erw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality_assoc]
  have hu := congrArg (fun q => q.hom.app (op U)) (representedSheafBaseChangeIso_unit f H)
  change ((inverseImageAdjunction f).unit.app (representedSheaf H)).hom.app (op U) ≫
    (representedSheafBaseChangeIso f H).hom.hom.app (op ((siteBaseChange f).obj U)) =
      (representedBaseChangeUnit f H).app (op U) at hu
  rw [← Category.assoc]
  erw [hu]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change representedFiberEvaluation s (baseChangedGroup f H)
      ((Scheme.pointSmallEtale s).toPresheafFiber ((siteBaseChange f).obj U)
        (pulledBackPoint f s U p) (representedPresheaf (baseChangedGroup f H))
        (ULift.up (Additive.ofMul ((Over.pullback f).map a.down.toMul)))) =
    representedPointPullback f s H
      (representedFiberEvaluation (s ≫ f) H
        ((Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber U p (representedPresheaf H) a))
  rw [representedFiberEvaluation_germ, representedFiberEvaluation_germ]
  apply ULift.ext
  change Additive.ofMul (pulledBackPoint f s U p ≫ (Over.pullback f).map a.down.toMul) =
    Additive.ofMul (pullbackFiberMulEquiv f s H (p ≫ a.down.toMul))
  exact congrArg Additive.ofMul
    ((Over.mapPullbackAdj f).homEquiv_naturality_right (X := Over.mk s) p a.down.toMul).symm

end Represented

section FiniteRepresentation
open Naturality
variable (R : CoefficientRepresentation L)

/-- Under an actual coefficient representation, the canonical germ-unit map
has exactly the canonical coefficient-point pullback. -/
theorem stalkUnit_fiberPointEquiv (a : coefficientFiber (s ≫ f) L) :
    (pulledBackRepresentation f R).fiberPointEquiv s (stalkUnit f s L a) =
      Additive.ofMul (pullbackFiberMulEquiv f s R.group (R.fiberPointEquiv (s ≫ f) a).toMul) := by
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let G := (Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hn := ConcreteCategory.congr_hom (stalkUnit_naturality f s L R.iso.inv) a
  have hr := ConcreteCategory.congr_hom (represented_stalkUnit f s R.group) (G.map R.iso.inv a)
  change (representedFiberEvaluation s (baseChangedGroup f R.group)
    (F.map ((inverseImage f).map R.iso.inv ≫ (representedSheafBaseChangeIso f R.group).hom)
      (stalkUnit f s L a))).down = _
  rw [F.map_comp]
  change (representedFiberEvaluation s (baseChangedGroup f R.group)
    (F.map (representedSheafBaseChangeIso f R.group).hom
      (F.map ((inverseImage f).map R.iso.inv) (stalkUnit f s L a)))).down = _
  change stalkUnit f s (representedSheaf R.group) (G.map R.iso.inv a) =
    F.map ((inverseImage f).map R.iso.inv) (stalkUnit f s L a) at hn
  rw [← hn]
  exact congrArg ULift.down hr

/-- The represented construction of stalk pullback is the inverse of the
canonical adjunction-unit map on actual germs. -/
theorem pullbackStalkEquiv_stalkUnit (a : coefficientFiber (s ≫ f) L) :
    pullbackStalkEquiv f s R (stalkUnit f s L a) = a := by
  apply (R.fiberPointEquiv (s ≫ f)).injective
  change (R.fiberPointEquiv (s ≫ f)) ((R.fiberPointEquiv (s ≫ f)).symm
    ((pullbackFiberMulEquiv f s R.group).symm.toAdditive
      ((pulledBackRepresentation f R).fiberPointEquiv s (stalkUnit f s L a)))) = _
  rw [AddEquiv.apply_symm_apply, stalkUnit_fiberPointEquiv]
  exact congrArg Additive.ofMul ((pullbackFiberMulEquiv f s R.group).symm_apply_apply _)

/-- The inverse represented stalk comparison is uniquely specified by its actual germ-unit map. -/
theorem stalkUnit_eq_inverse (a : coefficientFiber (s ≫ f) L) :
    stalkUnit f s L a = (pullbackStalkEquiv f s R).symm a :=
  (pullbackStalkEquiv f s R).injective
    ((pullbackStalkEquiv_stalkUnit f s L R a).trans ((pullbackStalkEquiv f s R).apply_symm_apply
      a).symm)

/-- Canonical stalk pullback is independent of the chosen actual coefficient representative. -/
theorem pullbackStalkEquiv_independent (T : CoefficientRepresentation L) :
    pullbackStalkEquiv f s R = pullbackStalkEquiv f s T := by
  have hi : (pullbackStalkEquiv f s R).symm = (pullbackStalkEquiv f s T).symm := by
    ext a
    exact (stalkUnit_eq_inverse f s L R a).symm.trans (stalkUnit_eq_inverse f s L T a)
  simpa only [AddEquiv.symm_symm] using congrArg AddEquiv.symm hi

/-- The finite represented view of the original all-coefficient stalk isomorphism. -/
def stalkUnitIso (R : CoefficientRepresentation L) :
    coefficientFiber (s ≫ f) L ≅ coefficientFiber s ((inverseImage f).obj L) :=
  let _ := R
  (StalkInverseImage.stalkUnitNatIso f s).app L

/-- The isomorphism has exactly the constructed germ-unit morphism, not merely the same source and
target. -/
theorem stalkUnitIso_hom : (stalkUnitIso f s L R).hom = stalkUnit f s L := rfl

end FiniteRepresentation

section Pointed
variable (x : Spec (CommRingCat.of K) ⟶ X) (hx : s ≫ f = x)

/-- The canonical represented stalk equivalence for a point-preserving map. -/
def pointedPullbackStalkEquiv (R : CoefficientRepresentation L) :
    coefficientFiber s ((inverseImage f).obj L) ≃+ coefficientFiber x L := by
  subst x
  exact Naturality.pullbackStalkEquiv f s R

/-- Its inverse is the canonical pointed unit-on-germs map. -/
theorem pointedStalkUnit_eq_inverse (R : CoefficientRepresentation L) (a : coefficientFiber x L) :
    pointedStalkUnit f s L x hx a = (pointedPullbackStalkEquiv f s L x hx R).symm a := by
  subst x
  exact stalkUnit_eq_inverse f s L R a

end Pointed

section CanonicalNaturality
open Naturality MarkedComparisonTransport
variable (R : CoefficientRepresentation L)

/-- Canonical stalk pullback is natural in every actual additive coefficient map. -/
theorem pullbackStalkEquiv_naturality {N : AbelianSheaf.{u, u + 1} X}
    (T : CoefficientRepresentation N) (q : L ⟶ N)
    (a : coefficientFiber s ((inverseImage f).obj L)) :
    pullbackStalkEquiv f s T
      (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map ((inverseImage
        f).map q) a) =
      ((Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1})).map q
        (pullbackStalkEquiv f s R a) := by
  let b := pullbackStalkEquiv f s R a
  have hb : stalkUnit f s L b = a :=
    (stalkUnit_eq_inverse f s L R b).trans ((pullbackStalkEquiv f s R).symm_apply_apply a)
  have hn := ConcreteCategory.congr_hom (stalkUnit_naturality f s L q) b
  change stalkUnit f s N
      (((Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1})).map q b) =
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map ((inverseImage
      f).map q)
      (stalkUnit f s L b) at hn
  rw [hb] at hn
  rw [← hn, pullbackStalkEquiv_stalkUnit]

/-- The point-coordinate formula of the canonical stalk equivalence. -/
theorem pullbackStalkEquiv_points (a : coefficientFiber s ((inverseImage f).obj L)) :
    R.fiberPointEquiv (s ≫ f) (pullbackStalkEquiv f s R a) =
      Additive.ofMul ((pullbackFiberMulEquiv f s R.group).symm
        ((pulledBackRepresentation f R).fiberPointEquiv s a).toMul) :=
  (R.fiberPointEquiv (s ≫ f)).apply_symm_apply _

/-- The actual pulled-back stalk action is the restriction of actual intrinsic
monodromy along the actual induced fundamental-group homomorphism. -/
theorem pullbackStalkEquiv_equivariant (γ : FiberAutGroup s)
    (a : coefficientFiber s ((inverseImage f).obj L)) :
    pullbackStalkEquiv f s R (stalkEvaluation s (pulledBackRepresentation f R) γ a) =
      stalkEvaluation (s ≫ f) R
        (Scheme.FiniteEtale.ClassificationNaturality.inducedGroupHom f s γ)
        (pullbackStalkEquiv f s R a) := by
  apply (R.fiberPointEquiv (s ≫ f)).injective
  rw [pullbackStalkEquiv_points, stalkEvaluation_points, stalkEvaluation_points,
    pullbackStalkEquiv_points]
  exact congrArg Additive.ofMul
    (Scheme.FiniteEtale.ClassificationNaturality.fiberBaseChange_equivariant
      f s γ (coefficientCover R.group) ((pulledBackRepresentation f R).fiberPointEquiv s a).toMul)

/-- Pointed canonical stalk pullback has exactly the pointed actual group restriction. -/
theorem pointedPullbackStalkEquiv_equivariant
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : s ≫ f = x)
    (γ : FiberAutGroup s) (a : coefficientFiber s ((inverseImage f).obj L)) :
    pointedPullbackStalkEquiv f s L x hx R
      (stalkEvaluation s (pulledBackRepresentation f R) γ a) =
      stalkEvaluation x R (Naturality.pointedGroupHom f s x hx γ)
        (pointedPullbackStalkEquiv f s L x hx R a) := by
  subst x
  exact pullbackStalkEquiv_equivariant f s L R γ a

end CanonicalNaturality

section SectionIdentity
variable {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B)
variable (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable (L : AbelianSheaf.{u, u + 1} B)

/-- On every genuine stalk element, the exact inverse-image Comp/Id section
coefficient map is the composite of canonical pointed stalk pullbacks. -/
theorem section_stalk_pullback (R : CoefficientRepresentation L)
    (a : coefficientFiber b ((inverseImage o).obj ((inverseImage p).obj L))) :
    ((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((inverseImageComp p o).inv.app L ≫
        eqToHom (congrArg (fun k : B ⟶ B => (inverseImage k).obj L) h) ≫
        (inverseImageId B).hom.app L) a =
      pointedPullbackStalkEquiv p (b ≫ o) L b (by simp [Category.assoc, h]) R
        (pointedPullbackStalkEquiv o b ((inverseImage p).obj L) (b ≫ o) rfl
          (Naturality.pulledBackRepresentation p R) a) := by
  let Ep := pointedPullbackStalkEquiv p (b ≫ o) L b (by simp [Category.assoc, h]) R
  let Eo := pointedPullbackStalkEquiv o b ((inverseImage p).obj L) (b ≫ o) rfl
    (Naturality.pulledBackRepresentation p R)
  let c := Ep (Eo a)
  have hp : pointedStalkUnit p (b ≫ o) L b (by simp [Category.assoc, h]) c = Eo a :=
    (pointedStalkUnit_eq_inverse p (b ≫ o) L b (by simp [Category.assoc, h]) R c).trans
      (Ep.symm_apply_apply _)
  have ho : pointedStalkUnit o b ((inverseImage p).obj L) (b ≫ o) rfl (Eo a) = a :=
    (pointedStalkUnit_eq_inverse o b ((inverseImage p).obj L) (b ≫ o) rfl
      (Naturality.pulledBackRepresentation p R) (Eo a)).trans (Eo.symm_apply_apply a)
  have hh := ConcreteCategory.congr_hom (section_stalkUnit b p o h L) c
  change ((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map _
    (pointedStalkUnit o b ((inverseImage p).obj L) (b ≫ o) rfl
      (pointedStalkUnit p (b ≫ o) L b (by simp [Category.assoc, h]) c)) = c at hh
  rw [hp, ho] at hh
  exact hh

end SectionIdentity

end AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientStalkBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage

universe u

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : S ⟶ X) («η» : Spec (.of Ω) ⟶ S)

/-- For finite represented coefficients this is the already constructed original isomorphism. -/
theorem stalkUnitNatIso_app_eq (L : AbelianSheaf.{u, u + 1} X)
    (R : CoefficientRepresentation L) :
    (stalkUnitNatIso f «η»).app L = CoefficientStalkBaseChange.stalkUnitIso f «η» L R := by
  apply Iso.ext
  exact (CoefficientStalkBaseChange.stalkUnitIso_hom f «η» L R).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 56186a24977fd3740dd1db18c6bfffb7b7978205c309ed9c4598458baae72450.
Definitions, hypotheses and universes are retained modulo native names. -/
