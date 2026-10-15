/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementTotalDerivedComparison.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 59]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # The actual installed derived direct image from the original Godement total -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The standard derived category of module sheaves used to compute direct image by Godement
totals. -/
local instance godementTotalStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The installed derived unit on the actual Godement totalizations. -/
def godementTotalDerivedUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    godementTotalPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⟶
      godementTotalPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  CategoryTheory.Functor.whiskerLeft (godementTotalPlus X) (derivedPushforwardPlusUnit f)

instance godementTotalDerivedUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (godementTotalDerivedUnit f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  exact godementTotalPlus_derivedPushforwardUnit_isIso f K

/-- The actual proved total augmentation transported by the installed derived functor. -/
def godementTotalDerivedAugmentation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f ⟶
      godementTotalPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  CategoryTheory.Functor.whiskerRight (godementTotalPlusUnit X)
    (DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f)

instance godementTotalDerivedAugmentation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (godementTotalDerivedAugmentation f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  have : IsIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit X).app K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _
      (godementTotalPlusUnit_quasiIso X K)
  exact inferInstanceAs (IsIso ((derivedPushforwardPlus f).map
    (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit X).app K))))

/-- Natural original-model comparison: actual direct image of the actual flasque total
represents the installed derived direct image of the original lower-bounded input. -/
def godementTotalDerivedPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    godementTotalPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ≅ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  asIso (godementTotalDerivedUnit f) ≪≫ (asIso (godementTotalDerivedAugmentation f)).symm

end AlgebraicGeometry.Scheme.Modules.Godement
