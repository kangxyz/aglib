/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SliceComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal

/-! # Original scheme pullback and the actual etale slice

The coefficient comparison is the existing inverse-image/restriction
isomorphism, followed by the actual slice equivalence. Its normalization is
checked on original terminal-object sections before applying Ext.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- Slice restriction followed by the actual slice equivalence is ordinary
restriction along the etale chart. -/
def sliceRestrictionEtaleIso :
    (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U ⋙
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).functor ≅
        etaleRestriction U.hom :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (Iso.refl _)) (by
    intro F G g
    ext V a
    rfl)

/-- Comparison with the original scheme inverse-image functor, not an
alternative coefficient definition. -/
def inverseImageSliceIso :
    inverseImage U.hom ≅
      (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U ⋙
        (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).functor :=
  inverseImageEtaleIso U.hom ≪≫ (sliceRestrictionEtaleIso U).symm

omit U in
/-- Under the original inverse-image/restriction comparison, pullback of
global sections is literal restriction to the postcomposed terminal object. -/
theorem globalSectionsPullback_etaleRestriction {S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    (F : AbelianSheaf.{u, u + 1} X) :
    globalSectionsPullback f F ≫
      ((inverseImageEtaleIso f).hom.app F).hom.app (op (etaleTerminal S)) =
      F.obj.map ((etaleTerminalIsTerminal X).from
        ((siteEtalePostcompose f).obj (etaleTerminal S))).op := by
  let := siteEtalePostcompose_continuous f
  let adj := (siteEtalePostcomposeAdj f).sheafPushforwardContinuous
    (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X)
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (inverseImageAdjunction f) adj F
  have h := congrArg
    (fun a : F ⟶ (directImage f).obj ((etaleRestriction f).obj F) =>
      a.hom.app (op (etaleTerminal X))) hu
  change ((inverseImageAdjunction f).unit.app F).hom.app (op (etaleTerminal X)) ≫
      ((inverseImageEtaleIso f).hom.app F).hom.app
        (op ((siteBaseChange f).obj (etaleTerminal X))) =
    F.obj.map ((siteEtalePostcomposeAdj f).counit.app (etaleTerminal X)).op at h
  change (((inverseImageAdjunction f).unit.app F).hom.app (op (etaleTerminal X)) ≫
      ((inverseImage f).obj F).obj.map (siteBaseChangeTerminalIso f).inv.op) ≫ _ = _
  rw [Category.assoc,
    ((inverseImageEtaleIso f).hom.app F).hom.naturality,
    ← Category.assoc]
  refine (congrArg (fun k => k ≫
    ((etaleRestriction f).obj F).obj.map (siteBaseChangeTerminalIso f).inv.op) h).trans ?_
  change F.obj.map ((siteEtalePostcomposeAdj f).counit.app (etaleTerminal X)).op ≫
    F.obj.map ((siteEtalePostcompose f).map (siteBaseChangeTerminalIso f).inv).op = _
  rw [← F.obj.map_comp, ← op_comp]
  congr 1
  congr 1
  exact (etaleTerminalIsTerminal X).hom_ext _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
