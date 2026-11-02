/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Flat base change of the original structure-sheaf isomorphism

These degree-zero section and sheaf comparisons are independent of properness
and formal functions. The original section pushout and affine-basis proofs are
moved intact from `Morphisms.Proper.ConnectedFibres`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual section map of a flat base change is invertible on each affine
chart lying over an affine target chart. -/
theorem isIso_app_pullback_snd_of_flat_of_isIso_c
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsIso f.c]
    (U : Y.Opens) (hU : IsAffineOpen U) (V : T.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) : IsIso ((pullback.snd f g).app V) := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  let H : IsPullback a b f g := IsPullback.of_hasPullback f g
  have hUV : b ⁻¹ᵁ V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro z hz
    change f (a z) ∈ U
    have hpoint : f (a z) = g (b z) :=
      congrArg (fun k : pullback f g ⟶ Y => k z) H.w
    rw [hpoint]
    exact hVU hz
  have hUY : b ⁻¹ᵁ V = a ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ b ⁻¹ᵁ V :=
    le_antisymm (le_inf hUV le_rfl) inf_le_right
  let comparison := AlgebraicGeometry.pushoutSection H hVU le_rfl hUY
  let : IsIso comparison :=
    AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
      H hVU le_rfl hUY hU hV (f.isCompact_preimage hU.isCompact)
        (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let : IsIso (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    infer_instance
  have hcomp : pushout.inr (f.appLE U (f ⁻¹ᵁ U) le_rfl) (g.appLE U V hVU) ≫
      comparison = b.app V := by
    dsimp only [comparison, AlgebraicGeometry.pushoutSection]
    rw [pushout.inr_desc]
    exact b.appLE_eq_app
  change IsIso (b.app V)
  rw [← hcomp]
  infer_instance

/-- Flat change of base preserves the actual structure-sheaf isomorphism for
a quasi-compact quasi-separated morphism. -/
theorem isIso_c_pullback_snd_of_flat_of_isIso_c
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsIso f.c] :
    IsIso (pullback.snd f g).c := by
  let b := pullback.snd f g
  let B := {V : T.Opens // IsAffineOpen V ∧
    ∃ U : Y.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U}
  have hB : Opens.IsBasis (Set.range (fun V : B => V.val)) := by
    have hrange : Set.range (fun V : B => V.val) =
        {V : T.Opens | IsAffineOpen V ∧ ∃ U : Y.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U} := by
      ext V
      constructor
      · rintro ⟨W, rfl⟩
        exact W.property
      · intro hV
        exact ⟨⟨V, hV⟩, rfl⟩
    rw [hrange]
    apply Opens.isBasis_iff_nbhd.mpr
    intro W x hx
    obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top (g x))
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (show x ∈ W ⊓ g ⁻¹ᵁ U from ⟨hx, hxU⟩)
    exact ⟨V, ⟨hV, U, hU, hVW.trans inf_le_right⟩, hxV, hVW.trans inf_le_left⟩
  let F : T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} b.base).obj
      (pullback f g).sheaf := ⟨b.c⟩
  have : IsIso F := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := fun V : B => V.val) hB ?_
    intro V
    obtain ⟨U, hU, hVU⟩ := V.property.2
    exact isIso_app_pullback_snd_of_flat_of_isIso_c f g U hU V.val V.property.1 hVU
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map F))

end AlgebraicGeometry.Scheme
