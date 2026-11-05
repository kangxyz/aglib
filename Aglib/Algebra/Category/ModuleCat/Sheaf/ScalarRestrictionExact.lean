/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingExact
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Exact and conservative original module-valued scalar restriction

Forgetting to abelian sheaves leaves restriction unchanged. Exactness follows
from that literal comparison and the conservative exact underlying functor.
No fullness, flatness or injective-preservation hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r s

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R : Type r} {S : Type s} [Ring R] [Ring S] (φ : R →+* S)
  [HasSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] hasSheafify

/-- Restriction changes only the sectionwise action of the actual ring map. -/
abbrev valuedScalarRestriction :
    CategoryTheory.Sheaf J (ModuleCat.{max u v} S) ⥤
      CategoryTheory.Sheaf J (ModuleCat.{max u v} R) :=
  sheafCompose J (ModuleCat.restrictScalars.{max u v} φ)

/-- The underlying sheaf, including all its restriction maps, is unchanged. -/
def valuedScalarRestrictionUnderlyingIso :
    valuedScalarRestriction J φ ⋙ underlying R J ≅ underlying S J := Iso.refl _

instance valuedScalarRestriction_reflectsIsomorphisms :
    (valuedScalarRestriction J φ).ReflectsIsomorphisms := by
  dsimp only [valuedScalarRestriction]
  infer_instance

instance valuedScalarRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (valuedScalarRestriction J φ) := by
  let : PreservesFiniteLimits (valuedScalarRestriction J φ ⋙ underlying R J) :=
    preservesFiniteLimits_of_natIso (valuedScalarRestrictionUnderlyingIso J φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (valuedScalarRestriction J φ) (underlying R J)

instance valuedScalarRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (valuedScalarRestriction J φ) := by
  let : PreservesFiniteColimits (valuedScalarRestriction J φ ⋙ underlying R J) :=
    preservesFiniteColimits_of_natIso (valuedScalarRestrictionUnderlyingIso J φ).symm
  exact preservesFiniteColimits_of_reflects_of_preserves
    (valuedScalarRestriction J φ) (underlying R J)

end ModuleCat.Sheaf
