/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResolutionPresheaf
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic
public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Aglib.Algebra.Homology.RightDerived.Represented

/-!
# Original represented cohomology of base-changed étale objects

The actual resolution presheaf is compared with original Ext-based cohomology
at each base-changed étale object. The Ext universe is independent of the
coefficient universe; no resizing of the original coefficient sheaf occurs.
The comparison is normalized by the native injective resolution and respects
original coefficient maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)

/-- Actual additive sections representation at the base-changed étale object. -/
def directImagePresheafRepresentedIso :
    preadditiveCoyoneda.obj (op
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U))) ≅
      directImagePresheaf f ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U) :=
  NatIso.ofComponents
    (fun F => (Sheaf.Hypercohomology.sectionsAddEquiv
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F).toAddCommGrpIso)
    (by
      intro F G a
      ext b
      exact Sheaf.Hypercohomology.sectionsEquiv_naturality
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) b a)

/-- Derive the original sections representation and commute exact evaluation
with native right-derived presheaves. -/
def directImagePresheafRepresentedDerivedIso (q : ℕ) :
    (preadditiveCoyoneda.obj (op
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)))).rightDerived q ≅
      resolutionCohomologyPresheaf f q ⋙
        (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U) :=
  (Functor.representedRightDerivedPostcompIso
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U))
    (directImagePresheaf f)
    ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U))
    (directImagePresheafRepresentedIso f U) q).symm

/-- The native represented constructor retains the entire original composition. -/
theorem directImagePresheafRepresentedDerivedIso_eq (q : ℕ) :
    directImagePresheafRepresentedDerivedIso f U q =
      Sheaf.ModuleCoefficients.rightDerivedNatIso (directImagePresheafRepresentedIso f U) q ≪≫
        Sheaf.ModuleCoefficients.rightDerivedPostcompIso (directImagePresheaf f)
          ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)) q := rfl

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Original represented-object cohomology computes the resolution presheaf's
value, through any supplied injective resolution. -/
def originalCohomologyResolutionEquivOfResolution
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U) ≃+
      ((resolutionCohomologyPresheaf f q).obj F).obj (op U) :=
  (I.extRightDerivedAddEquiv
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)) q).trans
    ((directImagePresheafRepresentedDerivedIso f U q).app F).addCommGroupIsoToAddEquiv

/-- Coefficient naturality retains the literal original Ext postcomposition. -/
theorem originalCohomologyResolutionEquivOfResolution_naturality
    {F G : AbelianSheaf.{u, u + 1} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {a : F ⟶ G}
    (φ : InjectiveResolution.Hom I J a) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    originalCohomologyResolutionEquivOfResolution f U J q
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ a) (add_zero q)) =
      ((resolutionCohomologyPresheaf f q).map a).app (op U)
        (originalCohomologyResolutionEquivOfResolution f U I q x) :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_naturality
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)) q
    (directImagePresheafRepresentedDerivedIso f U q) φ x

/-- The canonical native injective resolution gives the original value comparison. -/
def originalCohomologyResolutionEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U) ≃+
      ((resolutionCohomologyPresheaf f q).obj F).obj (op U) :=
  originalCohomologyResolutionEquivOfResolution f U (injectiveResolution F) q

/-- Changing the supplied resolution does not change the original value comparison. -/
theorem originalCohomologyResolutionEquiv_eq_ofResolution
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ) :
    originalCohomologyResolutionEquiv f U F q =
      originalCohomologyResolutionEquivOfResolution f U I q :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_eq
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)) q
    (directImagePresheafRepresentedDerivedIso f U q) (injectiveResolution F) I

end AlgebraicGeometry.Scheme.EtaleCohomology
