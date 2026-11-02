/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import
  Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedPostcompResolution

/-!
# Resolution cohomology presheaves of the actual direct image

Derive the original direct image followed by inclusion into presheaves. Exact
sheafification identifies this presheaf's sheafification with the actual higher
direct image. This is a resolution-level producer: the comparison of its values
with the original Ext-based cohomology on the fibre-product site is separate.
In positive degree no equality of sections with the cohomology presheaf is
asserted. All coefficients retain the original value universe `u + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original direct image viewed as a functor to abelian presheaves. -/
abbrev directImagePresheaf :
    AbelianSheaf.{u, u + 1} X ⥤ S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  directImage f ⋙ sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}

/-- The actual right-derived presheaf, computed by the native injective resolution. -/
abbrev resolutionCohomologyPresheaf (q : ℕ) :
    AbelianSheaf.{u, u + 1} X ⥤ S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (directImagePresheaf f).rightDerived q

/-- Sheafification of the underived presheaf is the original direct image. -/
def directImagePresheafSheafificationIso :
    directImagePresheaf f ⋙
        presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1} ≅
      directImage f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (directImage f)
      (sheafificationNatIso (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).symm ≪≫
    Functor.rightUnitor _

/-- Exact sheafification recovers the native higher direct image. The comparison
uses the original resolution and the original sheafification counit. -/
def resolutionCohomologySheafificationIso (q : ℕ) :
    resolutionCohomologyPresheaf f q ⋙
        presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1} ≅
      higherDirectImage f q :=
  (Sheaf.ModuleCoefficients.rightDerivedPostcompIso (directImagePresheaf f)
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}) q).symm ≪≫
  Sheaf.ModuleCoefficients.rightDerivedNatIso (directImagePresheafSheafificationIso f) q

/-- The canonical presheaf map into the underlying higher direct-image sheaf. -/
def resolutionCohomologyToHigherDirectImage (q : ℕ) :
    resolutionCohomologyPresheaf f q ⟶ higherDirectImage f q ⋙
      sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1} :=
  (Adjunction.whiskerRight (AbelianSheaf.{u, u + 1} X)
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})).homEquiv
      (resolutionCohomologyPresheaf f q) (higherDirectImage f q)
      (resolutionCohomologySheafificationIso f q).hom

/-- The whole native transpose is the original whiskered unit and comparison. -/
theorem resolutionCohomologyToHigherDirectImage_eq (q : ℕ) :
    resolutionCohomologyToHigherDirectImage f q =
      Functor.whiskerLeft (resolutionCohomologyPresheaf f q)
          (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).unit ≫
        Functor.whiskerRight (resolutionCohomologySheafificationIso f q).hom
          (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.ModuleCoefficients.rightDerivedPostcompIso_transpose_eq
    (directImagePresheaf f) (directImage f)
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (directImagePresheafSheafificationIso f) q

/-- The map is the original sheafification unit followed by the native comparison. -/
theorem resolutionCohomologyToHigherDirectImage_app (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (resolutionCohomologyToHigherDirectImage f q).app F =
      toSheafify (Scheme.smallEtaleTopology S)
          ((resolutionCohomologyPresheaf f q).obj F) ≫
        ((resolutionCohomologySheafificationIso f q).hom.app F).hom := by
  rw [resolutionCohomologyToHigherDirectImage_eq]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
