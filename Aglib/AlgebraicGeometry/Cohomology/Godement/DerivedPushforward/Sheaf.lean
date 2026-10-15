/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementDerivedSheaf.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 90]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The original sheaf's actual derived direct image from its Godement resolution

The integer-indexed augmentation is an actual quasi-isomorphism, and its flasque
resolution computes the installed derived direct image. The natural comparison
uses the installed derived unit and the image of that actual augmentation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The standard derived-category model for module sheaves on `X` in sheaf-resolution
comparisons. -/
local instance godementSheafStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original sheaf concentrated in integer degree zero, as a lower-bounded complex. -/
def godementSinglePlus (X : Scheme.{u}) : X.Modules ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor X.Modules 0) (fun _ => ⟨0, inferInstance⟩)

/-- The actual integer-indexed Godement resolution as a lower-bounded complex. -/
def godementResolutionIntPlus (X : Scheme.{u}) : X.Modules ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (godementResolutionInt X) (fun _ => ⟨0, inferInstance⟩)

/-- The actual quasi-isomorphism from the original sheaf in the lower-bounded category. -/
def godementResolutionIntPlusUnit (X : Scheme.{u}) :
    godementSinglePlus X ⟶ godementResolutionIntPlus X where
  app M := ObjectProperty.homMk ((godementResolutionIntUnit X).app M)
  naturality {M N} f := by
    apply ObjectProperty.hom_ext
    exact (godementResolutionIntUnit X).naturality f

instance godementResolutionIntPlusUnit_quasiIso (X : Scheme.{u}) (M : X.Modules) :
    QuasiIso ((godementResolutionIntPlusUnit X).app M).hom :=
  godementResolutionIntUnit_quasiIso X M

/-- The installed derived unit restricted to the original Godement resolutions. -/
def godementResolutionDerivedUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    godementResolutionIntPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⟶
      godementResolutionIntPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  CategoryTheory.Functor.whiskerLeft (godementResolutionIntPlus X) (derivedPushforwardPlusUnit f)

instance godementResolutionDerivedUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (godementResolutionDerivedUnit f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  exact isIso_derivedPushforwardPlusUnit_of_flasque f _
    (fun n => godementResolutionInt_isFlasque X M n)

/-- The actual Godement augmentation transported by the installed derived functor. -/
def godementResolutionDerivedAugmentation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    godementSinglePlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f ⟶
      godementResolutionIntPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  CategoryTheory.Functor.whiskerRight (godementResolutionIntPlusUnit X)
    (DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f)

instance godementResolutionDerivedAugmentation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (godementResolutionDerivedAugmentation f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  have : IsIso (DerivedCategory.Plus.Q.map ((godementResolutionIntPlusUnit X).app M)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _
      (godementResolutionIntPlusUnit_quasiIso X M)
  exact inferInstanceAs
    (IsIso ((derivedPushforwardPlus f).map
      (DerivedCategory.Plus.Q.map ((godementResolutionIntPlusUnit X).app M))))

/-- Natural original-model comparison: actual direct image of the original Godement
resolution represents the installed derived direct image of the original sheaf in degree zero. -/
def godementSheafDerivedPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    godementResolutionIntPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ≅
      godementSinglePlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  asIso (godementResolutionDerivedUnit f) ≪≫
    (asIso (godementResolutionDerivedAugmentation f)).symm

end AlgebraicGeometry.Scheme.Modules.Godement
