/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # The original Zariski to small-etale site functor

Open subschemes define a continuous finite-limit-preserving functor into the
original small-etale site. No replacement coefficient or topology is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

/-- The actual open immersion, regarded as an etale chart. -/
def opensToEtale : X.Opens ⥤ X.Etale where
  obj U := Etale.mk U.ι
  map f := (Etale.forget X).preimage (X.restrictFunctor.map f)
  map_id U := by
    apply (Etale.forget X).map_injective
    simp only [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply (Etale.forget X).map_injective
    simp

@[simp]
theorem opensToEtale_map_left {U V : X.Opens} (f : U ⟶ V) :
    ((opensToEtale X).map f).left = X.homOfLE f.le := by
  have h := (Etale.forget X).map_preimage
    (X := Etale.mk U.ι) (Y := Etale.mk V.ι) (X.restrictFunctor.map f)
  exact congrArg (fun a => a.left) h

/-- Forgetting the etale predicate recovers the native restriction functor. -/
def opensToEtaleForgetIso : opensToEtale X ⋙ Etale.forget X ≅ X.restrictFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    simp [opensToEtale])

/-- Restriction to open subschemes preserves the terminal object. -/
instance restrictFunctor_preservesTerminal :
    PreservesLimit (Functor.empty.{0} X.Opens) X.restrictFunctor := by
  apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
  apply (isLimitMapConeEmptyConeEquiv X.restrictFunctor (⊤ : X.Opens)).symm.toFun
  exact Over.mkIdTerminal.ofIso (Over.isoMk X.topIso (by simp)).symm

/-- Intersections compute the original pullbacks of open subschemes. -/
instance restrictFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan X.restrictFunctor := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro U V W f g _
  refine ⟨U ⊓ V, homOfLE inf_le_left, homOfLE inf_le_right, ?_, ?_⟩
  · refine ⟨⟨Subsingleton.elim _ _⟩, ⟨?_⟩⟩
    apply PullbackCone.IsLimit.mk _ (fun s => homOfLE (le_inf s.fst.le s.snd.le))
    all_goals intros; apply Subsingleton.elim
  · apply IsPullback.of_map_of_faithful (Over.forget X)
    exact isPullback_opens_inf_le f.le g.le

instance restrictFunctor_preservesFiniteLimits : PreservesFiniteLimits X.restrictFunctor := by
  let := preservesLimitsOfShape_pempty_of_preservesTerminal X.restrictFunctor
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

instance opensToEtale_preservesFiniteLimits : PreservesFiniteLimits (opensToEtale X) := by
  let : PreservesFiniteLimits (opensToEtale X ⋙ Etale.forget X) :=
    preservesFiniteLimits_of_natIso (opensToEtaleForgetIso X).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (opensToEtale X) (Etale.forget X)

/-- Zariski covers are jointly surjective families of the original etale charts. -/
theorem opensToEtale_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology X) (smallEtaleTopology X)
      (opensToEtale X) := by
  constructor
  intro U S hS
  change _ ∈ X.smallGrothendieckTopology (@Etale : MorphismProperty Scheme.{u}) _
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    mem_toGrothendieck_smallPretopology]
  intro x
  obtain ⟨V, f, hf, hx⟩ := hS x.1 x.2
  refine ⟨(opensToEtale X).obj V, (opensToEtale X).map f, ⟨x.1, hx⟩,
    Sieve.image_mem_functorPushforward _ S hf, inferInstance, ?_⟩
  rw [opensToEtale_map_left]
  apply Subtype.ext
  exact Scheme.homOfLE_apply f.le ⟨x.1, hx⟩

instance opensToEtale_isContinuous : (opensToEtale X).IsContinuous
    (Opens.grothendieckTopology X) (smallEtaleTopology X) := by
  let := flat_of_preservesFiniteLimits (opensToEtale X)
  exact Functor.isContinuous_iff_coverPreserving.mpr (opensToEtale_coverPreserving X)

end AlgebraicGeometry.Scheme
