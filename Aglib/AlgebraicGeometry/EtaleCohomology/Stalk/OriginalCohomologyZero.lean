/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomology
public import Aglib.Algebra.Homology.RightDerived.Postcomp.RepresentedSections

/-!
# Normalization of the original degree-zero cohomology comparison

Original degree-zero Ext classes are sent to the native derived-functor unit
applied to the original section. No independent comparison is chosen in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)

/-- The represented derived comparison preserves the original degree-zero unit. -/
theorem directImagePresheafRepresentedDerivedIso_zero_unit
    (F : AbelianSheaf.{u, u + 1} X) :
    (preadditiveCoyoneda.obj (op
        (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
          (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)))).toRightDerivedZero.app F ≫
      (directImagePresheafRepresentedDerivedIso f U 0).hom.app F =
    (directImagePresheafRepresentedIso f U).hom.app F ≫
      ((directImagePresheaf f).toRightDerivedZero.app F).app (op U) :=
  Functor.representedRightDerivedPostcompIso_zero_unit
    (directImagePresheaf f) ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U))
    (directImagePresheafRepresentedIso f U) F

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Original degree-zero Ext sections retain their actual section under the
native unit into the resolution cohomology presheaf. -/
theorem originalCohomologyResolutionEquiv_mk₀
    (F : AbelianSheaf.{u, u + 1} X)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) ⟶ F) :
    originalCohomologyResolutionEquiv f U F 0 (CategoryTheory.Abelian.Ext.mk₀ a) =
      ((directImagePresheaf f).toRightDerivedZero.app F).app (op U)
        (Sheaf.Hypercohomology.sectionsAddEquiv
          (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F a) :=
  (injectiveResolution F).extRightDerivedPostcompAddEquiv_mk₀
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)) (directImagePresheaf f)
    ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U))
    (directImagePresheafRepresentedIso f U) a

end AlgebraicGeometry.Scheme.EtaleCohomology
