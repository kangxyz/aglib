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
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.OriginalPullback
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
        ((siteEtalePostcompose f).obj (etaleTerminal S))).op :=
  Sheaf.SliceCohomology.unitSections_restriction
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
    (siteEtalePostcomposeAdj f) (inverseImageAdjunction f)
    (etaleTerminalIsTerminal X) (siteBaseChangeTerminalIso f) F

end AlgebraicGeometry.Scheme.EtaleCohomology
