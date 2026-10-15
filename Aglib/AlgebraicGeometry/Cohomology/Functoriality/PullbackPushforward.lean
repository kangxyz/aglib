/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat

/-! # The geometric pullback-pushforward unit and its derived transformation

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5PositiveUnitAffine.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`e2a5e17578652e168b9679659a38015d6f1a771effbcf83fb8d740b8cd83edfd`.
Selected declarations: geometricPlusUnit, derivedPositive, unitOnPlus, identityQLifting,
  positiveQLifting, derivedPositiveUnit, derivedPositiveUnit_app.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived category of module sheaves used for pullback/direct-image units. -/
local instance pullbackPushforwardDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

namespace Plus

/-- The geometric adjunction unit applied termwise to bounded-below module complexes. -/
def pullbackPushforwardUnit {P X : Scheme.{u}} (p : P ⟶ X) :
    𝟭 (CochainComplex.Plus X.Modules) ⟶
      (Scheme.Modules.pullback p).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward p).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    { f i := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (K.obj.X i)
      comm' i j _ :=
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality (K.obj.d i j)).symm }
  naturality {_ _} f := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext i
    exact (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality (f.hom.f i)

end Plus

/-- The bounded-below composite of derived flat pullback and derived direct image. -/
def derivedPullbackPushforwardPlus {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus X.Modules :=
  derivedFlatPullbackPlus p ⋙ derivedPushforwardPlus p

/-- The original geometric and derived units combined on bounded-below cochain representatives. -/
def derivedPullbackPushforwardPlusUnitOnPlus {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ derivedPullbackPushforwardPlus p :=
  Functor.whiskerRight (Plus.pullbackPushforwardUnit p) DerivedCategory.Plus.Q ≫
    Functor.whiskerLeft (Scheme.Modules.pullback p).mapCochainComplexPlus
      (derivedPushforwardPlusUnit p) ≫
    Functor.whiskerRight (Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit
      (derivedPushforwardPlus p)

/-- The localization lifting identifying Q followed by the derived identity with Q. -/
local instance identityQLifting (X : Scheme.{u}) : Localization.Lifting
    DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
    DerivedCategory.Plus.Q (𝟭 (DerivedCategory.Plus X.Modules)) :=
  ⟨Functor.rightUnitor _⟩

/-- The localization lifting for the flat pullback/direct-image derived composite. -/
local instance pullbackPushforwardQLifting {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    Localization.Lifting DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
      (DerivedCategory.Plus.Q ⋙ derivedPullbackPushforwardPlus p) (derivedPullbackPushforwardPlus
        p) := ⟨Iso.refl _⟩

/-- The pullback/direct-image unit descended to the bounded-below derived category for a flat
map. -/
def derivedPullbackPushforwardPlusUnit {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    𝟭 (DerivedCategory.Plus X.Modules) ⟶ derivedPullbackPushforwardPlus p :=
  Localization.liftNatTrans DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
    DerivedCategory.Plus.Q (DerivedCategory.Plus.Q ⋙ derivedPullbackPushforwardPlus p)
    (𝟭 (DerivedCategory.Plus X.Modules)) (derivedPullbackPushforwardPlus p)
      (derivedPullbackPushforwardPlusUnitOnPlus p)

lemma derivedPullbackPushforwardPlusUnit_app {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) :
    (derivedPullbackPushforwardPlusUnit p).app (DerivedCategory.Plus.Q.obj K) =
      (derivedPullbackPushforwardPlusUnitOnPlus p).app K := by
  simp [derivedPullbackPushforwardPlusUnit, Localization.liftNatTrans_app,
    Localization.Lifting.iso, identityQLifting, pullbackPushforwardQLifting]

end AlgebraicGeometry.Scheme.Modules
