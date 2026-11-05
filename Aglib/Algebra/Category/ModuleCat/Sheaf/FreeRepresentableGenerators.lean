/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentable
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Sites.Continuous

/-! # Original free module generators on a detecting subsite

Faithful restriction separates original maps; conservative restriction detects
proper subobjects using the original section equivalence. No fullness of the
scalar-forgetting functor is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf

universe c h r t a b

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type r) [Ring R] [HasSheafify J (ModuleCat.{max c h r t} R)]
    {B : Type a} [Category.{b} B] (K : GrothendieckTopology B) (s : B ⥤ C)
    [s.IsContinuous K J]

/-- The selected original free module generators on the actual subsite. -/
def freeGenerators : ObjectProperty (Sheaf J (ModuleCat.{max c h r t} R)) :=
  .ofObj (fun U : B => freeRepresentable J R (s.obj U))

variable [(s.sheafPushforwardContinuous (ModuleCat.{max c h r t} R) K J).Faithful]

include K in
/-- Original free module section maps separate original coefficient arrows. -/
theorem freeGenerators_isSeparating : (freeGenerators J R s).IsSeparating := by
  intro F G f g h
  apply (s.sheafPushforwardContinuous (ModuleCat.{max c h r t} R) K J).map_injective
  apply ObjectProperty.hom_ext
  ext U x
  let V := s.obj U.unop
  let z : freeRepresentable J R V ⟶ F :=
    (freeRepresentableSectionsEquiv J R V F).symm x
  have hz := h (freeRepresentable J R V) ⟨U.unop⟩ z
  have he := congrArg (freeRepresentableSectionsEquiv J R V G) hz
  change f.hom.app (op V) x = g.hom.app (op V) x
  simpa only [z, freeRepresentableSectionsEquiv_naturality,
    Equiv.apply_symm_apply] using he

variable [(s.sheafPushforwardContinuous (ModuleCat.{max c h r t} R) K J).ReflectsIsomorphisms]

include K in
/-- The same original section maps detect every proper original subobject. -/
theorem freeGenerators_isStrongGenerator : (freeGenerators J R s).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨freeGenerators_isSeparating J R K s, ?_⟩
  intro F G f hf h
  have he : IsIso ((s.sheafPushforwardContinuous
      (ModuleCat.{max c h r t} R) K J).map f).hom := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨?_, ?_⟩
    · intro x y hxy
      let V := s.obj U.unop
      change f.hom.app (op V) x = f.hom.app (op V) y at hxy
      apply (freeRepresentableSectionsEquiv J R V F).symm.injective
      apply (cancel_mono f).mp
      apply (freeRepresentableSectionsEquiv J R V G).injective
      simpa only [freeRepresentableSectionsEquiv_naturality,
        Equiv.apply_symm_apply] using hxy
    · intro x
      let V := s.obj U.unop
      obtain ⟨b, hb⟩ := h (freeRepresentable J R V) ⟨U.unop⟩
        ((freeRepresentableSectionsEquiv J R V G).symm x)
      refine ⟨freeRepresentableSectionsEquiv J R V F b, ?_⟩
      exact (freeRepresentableSectionsEquiv_naturality J R V b f).symm.trans
        ((congrArg (freeRepresentableSectionsEquiv J R V G) hb).trans
          ((freeRepresentableSectionsEquiv J R V G).apply_symm_apply x))
  have : IsIso ((sheafToPresheaf K (ModuleCat.{max c h r t} R)).map
      ((s.sheafPushforwardContinuous (ModuleCat.{max c h r t} R) K J).map f)) := he
  have : IsIso ((s.sheafPushforwardContinuous (ModuleCat.{max c h r t} R) K J).map f) :=
    isIso_of_reflects_iso _ (sheafToPresheaf K (ModuleCat.{max c h r t} R))
  exact isIso_of_reflects_iso f
    (s.sheafPushforwardContinuous (ModuleCat.{max c h r t} R) K J)

end ModuleCat.Sheaf
