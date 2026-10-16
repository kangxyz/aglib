/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion

/-!
# Closed pushforward and genuine extension by zero

On a specified Cartesian square, the original ordinary open base-change
isomorphism has an extension-by-zero adjoint. Its unit equation retains
the actual two open-extension units. The comparison restricts to an
isomorphism on the target open; closed-pushforward and extension-by-zero
stalk formulas then detect the same comparison globally.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- The extension-by-zero adjoint of the original open comparison and the
original source extension unit. -/
def closedPushforwardExtensionByZeroMap :
    pushforward b ⋙ extensionByZero j ⟶ extensionByZero a ⋙ pushforward f where
  app M := ((extensionByZeroRestrictAdjunction j).homEquiv _ _).symm
    ((pushforward b).map ((extensionByZeroRestrictAdjunction a).unit.app M) ≫
      (cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M))
  naturality {M N} k := by
    simp only [Functor.comp_map]
    apply ((extensionByZeroRestrictAdjunction j).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    have hη := (extensionByZeroRestrictAdjunction a).unit.naturality k
    simp only [Functor.id_map, Functor.comp_map] at hη
    rw [← Functor.map_comp_assoc, hη, Functor.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun q => (pushforward b).map
      ((extensionByZeroRestrictAdjunction a).unit.app M) ≫ q)
      ((cartesianOpenBaseChange a b f j h).inv.naturality ((extensionByZero a).map k))

/-- The adjoint comparison retains the original extension units and the
inverse original open base-change isomorphism. -/
@[reassoc]
theorem closedPushforwardExtensionByZeroMap_unit (M : W.Modules) :
    (extensionByZeroRestrictAdjunction j).unit.app ((pushforward b).obj M) ≫
        (restrictFunctor j).map ((closedPushforwardExtensionByZeroMap a b f j h).app M) =
      (pushforward b).map ((extensionByZeroRestrictAdjunction a).unit.app M) ≫
        (cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M) := by
  change (extensionByZeroRestrictAdjunction j).homEquiv _ _
    (((extensionByZeroRestrictAdjunction j).homEquiv _ _).symm _) = _
  exact ((extensionByZeroRestrictAdjunction j).homEquiv _ _).apply_symm_apply _

/-- Restricting the actual comparison to the target open is invertible,
without a closedness condition on the remaining morphisms. -/
theorem closedPushforwardExtensionByZeroMap_restrict_isIso (M : W.Modules) :
    IsIso ((restrictFunctor j).map
      ((closedPushforwardExtensionByZeroMap a b f j h).app M)) := by
  have hi : IsIso ((extensionByZeroRestrictAdjunction j).unit.app
      ((pushforward b).obj M) ≫ (restrictFunctor j).map
        ((closedPushforwardExtensionByZeroMap a b f j h).app M)) := by
    rw [closedPushforwardExtensionByZeroMap_unit]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

omit [IsOpenImmersion j] in
include h in
/-- Outside the target open, the actual closed pushforward of the source
extension has zero stalk. Only the original commutative square is used to
exclude points of the source open. -/
theorem isZero_closedPushforwardExtensionByZero_stalk_of_not_mem
    [IsClosedImmersion f] (x : X) (hx : x ∉ Set.range j) (M : W.Modules) :
    IsZero ((moduleStalk X x).obj
      ((pushforward f).obj ((extensionByZero a).obj M))) := by
  by_cases hxf : x ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hxf
    have hy : y ∉ Set.range a := by
      rintro ⟨z, rfl⟩
      apply hx
      exact ⟨b z, (congrArg (fun k : W ⟶ X => k z) h.w).symm⟩
    have hz := (ModuleCat.restrictScalars (f.stalkMap y).hom).map_isZero
      (isZero_extensionByZero_stalk_of_not_mem a y hy M)
    exact hz.of_iso ((pushforwardModuleStalkIso f f.isClosedEmbedding.isInducing y).app
      ((extensionByZero a).obj M))
  · exact isZero_pushforward_moduleStalk_of_not_mem f f.isClosedEmbedding.isClosed_range
      x hxf ((extensionByZero a).obj M)

/-- For a closed immersion, the same extension comparison is invertible on
all module sheaves, detected on its actual inside and outside stalk maps. -/
theorem closedPushforwardExtensionByZeroMap_isIso [IsClosedImmersion f]
    (M : W.Modules) : IsIso ((closedPushforwardExtensionByZeroMap a b f j h).app M) := by
  apply isIso_of_moduleStalk
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    let := closedPushforwardExtensionByZeroMap_restrict_isIso a b f j h M
    apply (NatIso.isIso_map_iff (restrictModuleStalkIso j y) _).mp
    change IsIso ((ModuleCat.restrictScalars (j.stalkMap y).hom).map
      ((moduleStalk V y).map ((restrictFunctor j).map
        ((closedPushforwardExtensionByZeroMap a b f j h).app M))))
    infer_instance
  · exact (isZero_extensionByZero_stalk_of_not_mem j x hx ((pushforward b).obj M)).isIso
      (isZero_closedPushforwardExtensionByZero_stalk_of_not_mem a b f j h x hx M) _

/-- The original extension comparison as a natural isomorphism, without QC,
Noetherianity or finite-presentation assumptions on the coefficient. -/
def closedPushforwardExtensionByZeroIso [IsClosedImmersion f] :
    pushforward b ⋙ extensionByZero j ≅ extensionByZero a ⋙ pushforward f := by
  letI : IsIso (closedPushforwardExtensionByZeroMap a b f j h) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact closedPushforwardExtensionByZeroMap_isIso a b f j h
  exact asIso (closedPushforwardExtensionByZeroMap a b f j h)

/-- The natural isomorphism retains the actual unit-defined exchange map. -/
@[simp]
theorem closedPushforwardExtensionByZeroIso_hom [IsClosedImmersion f] :
    (closedPushforwardExtensionByZeroIso a b f j h).hom =
      closedPushforwardExtensionByZeroMap a b f j h := rfl

end AlgebraicGeometry.Scheme.Modules
