/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Equiv.ComparisonComposite
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCohomology
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction

/-! # Original affine-test values of the relative comparison

Only the original represented cohomology groups are resized, as in the native
higher-image presheaf. The coefficient sheaf and its actual affine restriction
retain their original value universe. Transition naturality is separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- The whole original function-construction equation, with its source and target
fixed by the selected comparison before the four original edges are supplied. -/
def AffineValueFunctionConstruction {A B C D E : Type*}
    (e : A → E) (l : A → B) (c : B → C) (t : C → D) (r : D → E) : Prop :=
  e = fun z => r (t (c (l z)))

/-- Project the complete original constructor before substituting geometric carriers. -/
private theorem originalComparisonComposite_function
    {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    (l : A ≃+ B) (c : B ≃+ C) (t : D ≃+ C) (r : D ≃+ E) :
    AffineValueFunctionConstruction (AddEquiv.comparisonComposite l c t r).toEquiv.toFun
      l.toEquiv.toFun c.toEquiv.toFun t.symm.toEquiv.toFun r.toEquiv.toFun := rfl

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (U : S.AffineEtale)
  [HasExt.{s} (Sheaf ((smallEtaleTopology X).over
    ((siteBaseChange f).obj ((Scheme.AffineEtale.Spec S).obj U))) AddCommGrpCat.{u + 1})]
  [hPullbackExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
      (Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f))]

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj M).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f M q

local instance : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

local instance : Small.{u + 1}
    (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} (smallEtaleTopology X)
      (additiveCoefficient X M) q ((siteBaseChange f).obj ((Scheme.AffineEtale.Spec S).obj U))) :=
  originalCohomologyPresheaf_small f (additiveCoefficient X M) q
    (op ((Scheme.AffineEtale.Spec S).obj U))

/-- The component of the relative comparison on a literal native affine étale
test, through the actual fibre-product comparison and original group resize. -/
def higherDirectImageAffineValueEquiv :
    ((EtaleAffineBasis.abelianRestriction S).obj
      (additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M))).obj.obj
        (op U) ≃+
    (smallOriginalCohomologyPresheaf f (additiveCoefficient X M) q).obj
      (op ((Scheme.AffineEtale.Spec S).obj U)) :=
  AddEquiv.comparisonComposite AddEquiv.ulift
    (higherDirectImageAffineSectionsEquiv.{u, e} f ((Scheme.AffineEtale.Spec S).obj U).hom M q)
    (fibreProductCohomologyEquiv.{u, w, s, e} f
      ((Scheme.AffineEtale.Spec S).obj U) (additiveCoefficient X M) q)
    Shrink.addEquiv.symm

/-- The whole underlying function of the original affine value comparison, with
all four original edge carriers inferred from the canonical constructor. -/
theorem higherDirectImageAffineValueEquiv_function :
    AffineValueFunctionConstruction
      (higherDirectImageAffineValueEquiv.{u, w, s, e} f M q U).toEquiv.toFun
      AddEquiv.ulift.toEquiv.toFun
      (higherDirectImageAffineSectionsEquiv.{u, e} f
        ((Scheme.AffineEtale.Spec S).obj U).hom M q).toEquiv.toFun
      (fibreProductCohomologyEquiv.{u, w, s, e} f
        ((Scheme.AffineEtale.Spec S).obj U) (additiveCoefficient X M) q).symm.toEquiv.toFun
      Shrink.addEquiv.{u + 1, w}.symm.toEquiv.toFun := by
  have h := originalComparisonComposite_function
    (A := ((EtaleAffineBasis.abelianRestriction S).obj
      (additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M))).obj.obj
      (op U))
    (E := (smallOriginalCohomologyPresheaf f (additiveCoefficient X M) q).obj
      (op ((Scheme.AffineEtale.Spec S).obj U))) AddEquiv.ulift
    (higherDirectImageAffineSectionsEquiv.{u, e} f ((Scheme.AffineEtale.Spec S).obj U).hom M q)
    (fibreProductCohomologyEquiv.{u, w, s, e} f
      ((Scheme.AffineEtale.Spec S).obj U) (additiveCoefficient X M) q)
    Shrink.addEquiv.symm
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
