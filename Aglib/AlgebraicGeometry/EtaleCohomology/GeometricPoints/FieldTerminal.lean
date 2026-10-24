/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # The actual identity point over a separably closed field

The identity pointed terminal object is initial in the original neighborhood
category. Consequently its original germ is an isomorphism for every presheaf,
not just sheaves. No cohomology or replacement point model is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The actual identity point of the fixed terminal etale object. -/
def fieldTerminalPoint :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj (etaleTerminal (Spec (.of Ω))) :=
  𝟙 (Over.mk (𝟙 (Spec (.of Ω))))

/-- The original pointed identity object is initial: its unique arrow to a
pointed neighborhood is precisely that neighborhood's given point. -/
def fieldTerminalPointIsInitial :
    IsInitial ((pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.elementsMk
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω)) := by
  refine IsInitial.ofUniqueHom (fun d =>
    { hom := MorphismProperty.Over.homMk d.val.left (Over.w d.val)
      map_val := ?_ }) ?_
  · apply Over.OverMorphism.ext
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  · intro d a
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    have h := congrArg (fun k => k.left) a.map_val
    change 𝟙 _ ≫ a.hom.left = d.val.left at h
    exact (Category.id_comp a.hom.left).symm.trans h

/-- The literal terminal germ is invertible for every original presheaf. -/
instance fieldTerminalGerm_isIso
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω) P) :=
  isIso_ι_of_isTerminal (fieldTerminalPointIsInitial Ω).op
    ((Functor.Elements.π (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber).op ⋙ P)

end AlgebraicGeometry.Scheme.EtaleCohomology
