/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleProductTests
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleInverseImageInjectives
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.Algebra.Homology.RightDerived.Precomp
public import Aglib.Algebra.Homology.RightDerived.Postcomp

/-! # Original higher images of source étale charts

The actual product-test pushforward is the original chart restriction followed
by its original direct image and the original base direct image. Native
composition and the étale restriction comparison identify it with restriction
followed directly by the composite geometric morphism. Exact restriction
preserves injectives, so the native precomposition comparison computes all
higher images. No acyclicity of an intermediate open direct image is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Etale)

/-- The unchanged native direct image of the original product-test coefficient. -/
abbrev sourceEtaleImage : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S :=
  etaleProductSheaf U ⋙ directImage f

instance sourceEtaleImage_additive : (sourceEtaleImage f U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The source chart remains the original étale restriction and the composite
map remains the original geometric composite. -/
def sourceEtaleImageRestrictionIso :
    sourceEtaleImage f U ≅ etaleRestriction U.hom ⋙ directImage (U.hom ≫ f) :=
  Functor.associator (etaleRestriction U.hom) (directImage U.hom) (directImage f) ≪≫
    Functor.isoWhiskerLeft (etaleRestriction U.hom) (directImageCompIso f U.hom)

/-- The genuine inverse-image comparison is inserted only at the coefficient. -/
def sourceEtaleImageInverseIso :
    sourceEtaleImage f U ≅ inverseImage U.hom ⋙ directImage (U.hom ≫ f) :=
  sourceEtaleImageRestrictionIso f U ≪≫
    Functor.isoWhiskerRight (inverseImageEtaleIso U.hom).symm (directImage (U.hom ≫ f))

/-- The native higher image of the chart sequence is the original higher direct
image of the original restricted coefficient, in the same natural degree. -/
def sourceEtaleImageRightDerivedIso (q : ℕ) :
    (sourceEtaleImage f U).rightDerived q ≅
      inverseImage U.hom ⋙ higherDirectImage (U.hom ≫ f) q :=
  Functor.rightDerivedNatIsoOfAdditive (sourceEtaleImageInverseIso f U) q ≪≫
    Functor.rightDerivedPrecompIso (inverseImage U.hom) (directImage (U.hom ≫ f)) q

/-- The forward higher comparison retains the original derived natural
transformation and the native exact-precomposition comparison. -/
theorem sourceEtaleImageRightDerivedIso_hom (q : ℕ) :
    (sourceEtaleImageRightDerivedIso f U q).hom =
      NatTrans.rightDerived (sourceEtaleImageInverseIso f U).hom q ≫
        (Functor.rightDerivedPrecompIso (inverseImage U.hom)
          (directImage (U.hom ≫ f)) q).hom := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
