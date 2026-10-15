/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Presentation transport along compatible site functors

The local pushforward functors preserve colimits under the stated continuous,
cocontinuous, left-adjoint and structure-ring isomorphism hypotheses.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w' t t'
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

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

end AlgebraicGeometry.Scheme.Modules
