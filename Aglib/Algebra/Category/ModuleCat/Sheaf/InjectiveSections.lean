/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Injectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Aglib.Algebra.Category.ModuleCat.AB

/-!
# Original sections of injective constant-ring module sheaves

Restriction to the actual slice preserves injectives. At the terminal object
of that slice, the original constant-sheaf adjunction has a left exact left
adjoint, so its evaluation right adjoint also preserves injectives. Thus the
actual section module of an injective module-valued sheaf is injective.
This concerns sections of injectives, not stalks of injectives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]

attribute [local instance] hasSheafify

/-- The original section evaluation of constant-ring module sheaves preserves injective objects. -/
instance sections_preservesInjectiveObjects (U : C) :
    ((sheafSections J (ModuleCat.{max c h} Λ)).obj (op U)).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    let := hI
    let A := ModuleCat.{max c h} Λ
    let : (J.overPullback A U).PreservesInjectiveObjects :=
      CategoryTheory.Sheaf.SliceCohomology.overPullback_preservesInjectiveObjects J A U
    let : PreservesFiniteLimits (constantSheaf (J.over U) A) := by
      change PreservesFiniteLimits (Functor.const (Over U)ᵒᵖ ⋙ presheafToSheaf (J.over U) A)
      infer_instance
    exact (constantSheafAdj (J.over U) A Over.mkIdTerminal).map_injective
      ((J.overPullback A U).obj I) inferInstance

/-- Its actual section carrier has the native module extension property. -/
theorem moduleInjective_sections (I : Sheaf J (ModuleCat.{max c h} Λ)) [Injective I] (U : C) :
    Module.Injective Λ (I.obj.obj (op U)) := by
  let : Injective (I.obj.obj (op U)) :=
    Functor.injective_obj ((sheafSections J (ModuleCat.{max c h} Λ)).obj (op U)) I
  exact Module.injective_module_of_injective_object Λ (I.obj.obj (op U))

end ModuleCat.Sheaf
