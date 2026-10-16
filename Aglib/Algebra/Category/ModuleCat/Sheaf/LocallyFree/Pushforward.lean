/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Local-basis pushforward along compatible site functors

Relocated from `Aglib/AlgebraicGeometry/Modules/LocallyFree/Restriction.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `d7d645bfbda89e87d27ed0de091b3f6cfe2cb90934c5a1c80d787d2c67e1a852`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w' t t'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section General
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {D : Type t} [Category.{t'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (K.over U) AddCommGrpCat.{u}]
  [∀ U, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
  (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
  [G.IsLeftAdjoint] [IsIso φ]
  [∀ U, (Over.post (X := U) G).IsContinuous (K.over U) (J.over (G.obj U))]
  [HasPullbacks C] [HasPullbacks D]

/-- Transport a local basis by a continuous, cocontinuous left adjoint on
sites which carries the structure sheaf isomorphically to the target one. -/
def pushforwardLocalBasis {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] :
    SheafOfModules.LocalGeneratorsData ((SheafOfModules.pushforward φ).obj M) :=
  (q.quasiCoherentData.pushforward G φ η
    (localBasisPushforward_preservesColimits G φ)).localGeneratorsData

instance pushforwardLocalBasis_isLocallyFreeData {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] :
    (pushforwardLocalBasis G φ η q).IsLocallyFreeData where
  isIso i := by
    dsimp [pushforwardLocalBasis, SheafOfModules.QuasicoherentData.localGeneratorsData,
      SheafOfModules.QuasicoherentData.pushforward]
    rw [SheafOfModules.Presentation.map_π_eq]
    dsimp only [SheafOfModules.LocalGeneratorsData.quasiCoherentData]
    infer_instance

instance pushforwardLocalBasis_isFiniteType {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    (pushforwardLocalBasis G φ η q).IsFiniteType where
  isFiniteType i := by
    let := hq.isFiniteType i.2.1
    constructor
    change Finite (q.generators i.2.1).I
    infer_instance

end General

end SheafOfModules
