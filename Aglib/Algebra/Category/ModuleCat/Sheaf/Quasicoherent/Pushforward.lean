/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Presentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite-presentation transport along compatible site functors

Relocated from `Aglib/AlgebraicGeometry/Modules/FinitePresentation/Transport.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `e247b47da51a5aa5c8b176240e619d49a2c6188c347b34edbecc002bf2a7cc3d`.
Relocated from `Aglib/AlgebraicGeometry/Modules/FinitePresentation/Locality.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `aaa8f811926c9494b46ab8dd1236beec0d5df254385ca5f9d2295a857e09b28f`.
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

omit [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (K.over U) AddCommGrpCat.{u}]
  [∀ U, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The local restriction functors used to transport a basis preserve colimits. -/
theorem localBasisPushforward_preservesColimits (U : D) (V : C) (f : G.obj U ⟶ V) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (R := R.over V)
        (F := Over.post (X := U) G ⋙ Over.map f)
        (((Over.forget U).sheafPushforwardContinuous RingCat.{u} (K.over U) K).map φ)) := by
  let G' := Over.post (X := U) G ⋙ Over.map f
  have : G'.IsContinuous (K.over U) (J.over V) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over U) (J.over V) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over U ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over U) (J.over V)).obj (R.over V) :=
    ((Over.forget U).sheafPushforwardContinuous RingCat.{u} (K.over U) K).map φ
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end General

section Transport
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
  [hpost : ∀ U, (Over.post (X := U) G).IsContinuous (K.over U) (J.over (G.obj U))]
  [HasPullbacks C] [HasPullbacks D]

include η

/-- The finite local presentations are carried by the same site functor as
ordinary quasicoherent data; both finite index types are unchanged. -/
theorem finitePresentation_pushforward_of_isLeftAdjoint
    (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let q' := q.pushforward G φ η (SheafOfModules.localBasisPushforward_preservesColimits G φ)
  have hq' : q'.IsFinitePresentation := by
    constructor
    intro i
    dsimp [q', SheafOfModules.QuasicoherentData.pushforward]
    infer_instance
  refine ⟨q'.shrink, ?_⟩
  constructor
  intro i
  dsimp [SheafOfModules.QuasicoherentData.shrink]
  infer_instance

end Transport

end SheafOfModules
