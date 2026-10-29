/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResolutionPresheaf
public import
  Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedPostcompResolution

/-! # The original presheaf-to-higher-image map on resolution homology

The existing sheafification comparison is normalized on any supplied actual
integer resolution. Both the original sheafification unit and the actual
termwise counit are retained. No sections-versus-cohomology isomorphism is
assumed in positive degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original comparison into the higher-image sheaf is the actual
sheafification unit on resolution homology, followed by native exact
sheafification and the original termwise direct-image counit. -/
theorem resolutionCohomologyToHigherDirectImage_resolution
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ) :
    (resolutionCohomologyToHigherDirectImage f q).app F ≫
        (I.isoRightDerivedObjCochain (directImage f) q).hom.hom =
      (I.isoRightDerivedObjCochain (directImagePresheaf f) q).hom ≫
        toSheafify (Scheme.smallEtaleTopology S)
          ((((directImagePresheaf f).mapHomologicalComplex (.up ℤ)).obj
            I.cochainComplex).homology (q : ℤ)) ≫
        (((((directImagePresheaf f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex).sc (q : ℤ)).mapHomologyIso
            (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})).inv.hom ≫
        (homologyMap ((NatTrans.mapHomologicalComplex
          (directImagePresheafSheafificationIso f).hom (.up ℤ)).app I.cochainComplex)
            (q : ℤ)).hom := by
  exact Sheaf.ModuleCoefficients.rightDerivedPostcompIso_transpose_resolution_cochain
    (directImagePresheaf f) (directImage f)
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (directImagePresheafSheafificationIso f) I q

end AlgebraicGeometry.Scheme.EtaleCohomology
