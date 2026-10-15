/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Finite coproducts of exact functors

A finite coproduct of functors into an abelian category preserves finite limits or
finite colimits when every summand does. The comparison uses the actual pointwise
colimit and the finite biproduct comparison between colimits and limits.
-/


/-!
Source: `Quillen/CategoryTheory/Abelian/FiniteCoproductFunctor.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 55]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian D]
variable {I : Type*} [Finite I] (F : I → C ⥤ D)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A finite coproduct of left exact functors is left exact. -/
theorem preservesFiniteLimits_coproduct [∀ i, PreservesFiniteLimits (F i)] :
    PreservesFiniteLimits (∐ F) := by
  let d := Discrete.functor F
  have : PreservesFiniteLimits d.flip :=
    preservesFiniteLimits_of_evaluation _ (fun i => by
      change PreservesFiniteLimits (F i.as)
      infer_instance)
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := D)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  exact preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim d).symm

/-- A finite coproduct of right exact functors is right exact. -/
theorem preservesFiniteColimits_coproduct [∀ i, PreservesFiniteColimits (F i)] :
    PreservesFiniteColimits (∐ F) := by
  let d := Discrete.functor F
  have : PreservesFiniteColimits d.flip :=
    preservesFiniteColimits_of_evaluation _ (fun i => by
      change PreservesFiniteColimits (F i.as)
      infer_instance)
  exact preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim d).symm

end CategoryTheory.Limits
