/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomology
public import Aglib.Algebra.Homology.RightDerived.Postcomp.RepresentedSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ExtSourceNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ExactPostcomposition
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality

/-! # Original restriction maps for higher direct-image cohomology -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u v u₁ v₁ u₂ v₂ w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)

/-- The actual represented section comparisons respect original étale restrictions. -/
theorem directImagePresheafRepresentedIso_restriction :
    preadditiveCoyoneda.map
        (((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
          (Scheme.smallEtaleTopology X)).map ((siteBaseChange f).map g)).op) ≫
      (directImagePresheafRepresentedIso f V).hom =
    (directImagePresheafRepresentedIso f U).hom ≫
      Functor.whiskerLeft (directImagePresheaf f)
        ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).map g.op) := by
  ext F a
  exact Sheaf.SliceCohomology.freeSections_naturality
    (Scheme.smallEtaleTopology X) ((siteBaseChange f).map g) F a

/-- Native represented-derived comparisons respect the original restriction map. -/
theorem directImagePresheafRepresentedDerivedIso_restriction (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    ((preadditiveCoyoneda.map
        (((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
          (Scheme.smallEtaleTopology X)).map
            ((siteBaseChange f).map g)).op)).rightDerived q).app F ≫
      (directImagePresheafRepresentedDerivedIso f V q).hom.app F =
    (directImagePresheafRepresentedDerivedIso f U q).hom.app F ≫
      ((resolutionCohomologyPresheaf f q).obj F).map g.op :=
  by
  have h := Functor.representedRightDerivedPostcompIso_source
    (directImagePresheaf f) (directImagePresheafRepresentedIso f U)
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
      (Scheme.smallEtaleTopology X)).map ((siteBaseChange f).map g))
    ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).map g.op)
    (directImagePresheafRepresentedIso f V) (directImagePresheafRepresentedIso_restriction f g) q
  exact congrArg (fun η => η.app F) h

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Restriction of original Ext cohomology is the actual resolution-presheaf restriction. -/
theorem originalCohomologyResolutionEquiv_restriction
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    originalCohomologyResolutionEquiv f V F q
      ((Sheaf.LargeCohomology.presheaf.{w, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q).map ((siteBaseChange f).map g).op x) =
      ((resolutionCohomologyPresheaf f q).obj F).map g.op
        (originalCohomologyResolutionEquiv f U F q x) :=
  (injectiveResolution F).extRightDerivedPostcompAddEquiv_source
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U))
    (directImagePresheaf f) (directImagePresheafRepresentedIso f U)
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
      (Scheme.smallEtaleTopology X)).map ((siteBaseChange f).map g))
    ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).map g.op)
    (directImagePresheafRepresentedIso f V) (directImagePresheafRepresentedIso_restriction f g) q x

end AlgebraicGeometry.Scheme.EtaleCohomology
