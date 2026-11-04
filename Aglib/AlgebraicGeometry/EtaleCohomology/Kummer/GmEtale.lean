/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GlobalUnits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # The original multiplicative coefficient on an etale chart

Only etale scheme maps are used. The actual inverse-image comparison is
normalized by the original unit map and retains the literal global units.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]

/-- Literal etale restriction of the original Gm is the same original Gm on the chart. -/
def gmEtaleRestrictionIso : (etaleRestriction f).obj (gm X) ≅ gm S :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft (siteEtalePostcompose f).op (gmGlobalUnitsIso X) ≪≫
      (gmGlobalUnitsIso S).symm)

/-- The restriction comparison preserves the actual unit-valued section. -/
theorem gmEtaleRestrictionIso_hom_units (U : S.Etaleᵒᵖ)
    (a : ((etaleRestriction f).obj (gm X)).obj.obj U) :
    unitsSections S U ((gmEtaleRestrictionIso f).hom.hom.app U a) =
      unitsSections X ((siteEtalePostcompose f).op.obj U) a := by
  change (unitsSections S U) ((unitsSections S U).symm
    ((unitsSections X ((siteEtalePostcompose f).op.obj U)) a)) = _
  exact AddEquiv.apply_symm_apply _ _

/-- The actual inverse-image coefficient comparison for an etale map. -/
def gmEtalePullbackIso : (inverseImage f).obj (gm X) ≅ gm S :=
  (inverseImageEtaleIso f).app (gm X) ≪≫ gmEtaleRestrictionIso f

/-- The chosen comparison is adjoint to the original function-unit map. -/
theorem gmEtalePullbackIso_unit :
    (inverseImageAdjunction f).unit.app (gm X) ≫
      (directImage f).map (gmEtalePullbackIso f).hom = gmUnit f := by
  change (inverseImageAdjunction f).unit.app (gm X) ≫
    (directImage f).map (((inverseImageEtaleIso f).hom.app (gm X)) ≫
      (gmEtaleRestrictionIso f).hom) = _
  rw [Functor.map_comp, ← Category.assoc, inverseImageEtaleIso_unit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  apply (unitsSections S ((siteBaseChange f).op.obj U)).injective
  change unitsSections S ((siteBaseChange f).op.obj U)
    ((gmEtaleRestrictionIso f).hom.hom.app ((siteBaseChange f).op.obj U)
      ((gm X).obj.map ((siteEtalePostcomposeAdj f).counit.app U.unop).op a)) =
        unitsSections S ((siteBaseChange f).op.obj U) ((gmUnit f).hom.app U a)
  rw [gmEtaleRestrictionIso_hom_units]
  apply Additive.toMul.injective
  exact (unitsSections_naturality X
    ((siteEtalePostcomposeAdj f).counit.app U.unop).op a).trans
      (gmUnit_sections f U a).symm

/-- The original adjoint coefficient map itself, with no supplied isomorphism. -/
theorem gmUnit_adjoint_etale :
    torsorAdjunctionCoefficient f (q := gmUnit f) = (gmEtalePullbackIso f).hom := by
  let e := (inverseImageAdjunction f).homEquiv (gm X) (gm S)
  change e.symm (gmUnit f) = (gmEtalePullbackIso f).hom
  apply e.injective
  exact (e.apply_symm_apply (gmUnit f)).trans (gmEtalePullbackIso_unit f).symm

/-- Etaleness is the actual hypothesis making the original Gm coefficient map invertible. -/
instance gmUnitAdjointIsIsoOfEtale :
    IsIso (torsorAdjunctionCoefficient f (q := gmUnit f)) := by
  rw [gmUnit_adjoint_etale]
  infer_instance

variable {T : Scheme.{u}} (g : T ⟶ S) [Etale g]

/-- Literal units restriction has the original composition comparison. -/
theorem gmEtaleRestrictionIso_comp :
    (etaleRestrictionComp f g).hom.app (gm X) ≫
      (etaleRestriction g).map (gmEtaleRestrictionIso f).hom ≫
        (gmEtaleRestrictionIso g).hom = (gmEtaleRestrictionIso (g ≫ f)).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  apply (unitsSections T U).injective
  change unitsSections T U
    ((gmEtaleRestrictionIso g).hom.hom.app U
      ((gmEtaleRestrictionIso f).hom.hom.app ((siteEtalePostcompose g).op.obj U)
        ((gm X).obj.map ((siteEtalePostcomposeComp f g).hom.app U.unop).op a))) =
      unitsSections T U ((gmEtaleRestrictionIso (g ≫ f)).hom.hom.app U a)
  rw [gmEtaleRestrictionIso_hom_units, gmEtaleRestrictionIso_hom_units,
    gmEtaleRestrictionIso_hom_units]
  apply Additive.toMul.injective
  exact (unitsSections_naturality X
    ((siteEtalePostcomposeComp f g).hom.app U.unop).op a).trans (by
        change Units.map (Scheme.Hom.appTop (𝟙 U.unop.left)).hom.toMonoidHom _ = _
        rw [Scheme.Hom.id_appTop]
        rfl)

/-- The original inverse-image Gm isomorphisms compose with the actual inverse-image compositor. -/
theorem gmEtalePullbackIso_comp :
    (inverseImageComp f g).hom.app (gm X) ≫
      (inverseImage g).map (gmEtalePullbackIso f).hom ≫
        (gmEtalePullbackIso g).hom = (gmEtalePullbackIso (g ≫ f)).hom := by
  have hn := (inverseImageEtaleIso g).hom.naturality (gmEtaleRestrictionIso f).hom
  change (inverseImage g).map (gmEtaleRestrictionIso f).hom ≫
      (inverseImageEtaleIso g).hom.app (gm S) =
    (inverseImageEtaleIso g).hom.app ((etaleRestriction f).obj (gm X)) ≫
      (etaleRestriction g).map (gmEtaleRestrictionIso f).hom at hn
  simp only [gmEtalePullbackIso, Iso.trans_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((inverseImage g).map (gmEtaleRestrictionIso f).hom), hn]
  rw [Category.assoc]
  calc
    _ = ((inverseImageComp f g).hom.app (gm X) ≫
        (inverseImage g).map ((inverseImageEtaleIso f).hom.app (gm X)) ≫
          (inverseImageEtaleIso g).hom.app ((etaleRestriction f).obj (gm X))) ≫
        (etaleRestriction g).map (gmEtaleRestrictionIso f).hom ≫
          (gmEtaleRestrictionIso g).hom := by simp only [Category.assoc]
    _ = ((inverseImageEtaleIso (g ≫ f)).hom.app (gm X) ≫
        (etaleRestrictionComp f g).hom.app (gm X)) ≫
        (etaleRestriction g).map (gmEtaleRestrictionIso f).hom ≫
          (gmEtaleRestrictionIso g).hom := by rw [inverseImageEtaleIso_comp]
    _ = _ := by
      simp only [Category.assoc]
      rw [gmEtaleRestrictionIso_comp]

/-- The literal triangle version used by the fibre-product cohomology restriction. -/
theorem gmEtalePullbackIso_triangle (q : T ⟶ X) [Etale q] (hq : q = g ≫ f) :
    (pullbackTriangleIso q f g hq.symm).inv.app (gm X) ≫
      (gmEtalePullbackIso q).hom =
    (inverseImage g).map (gmEtalePullbackIso f).hom ≫
      (gmEtalePullbackIso g).hom := by
  subst q
  change (inverseImageComp f g).inv.app (gm X) ≫
      (gmEtalePullbackIso (g ≫ f)).hom = _
  apply (cancel_epi ((inverseImageComp f g).hom.app (gm X))).mp
  simpa only [Iso.hom_inv_id_app_assoc, Category.assoc] using
    (gmEtalePullbackIso_comp f g).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
