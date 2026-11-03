/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian

/-!
# Ordinary trace pullback and its actual base-change evaluation

The ordinary adjoint of an inverse trace retains the original geometric counit.
The base-change equation is an equality of sheaf maps for the actual Cartesian
square. Neither faithfulness of sections nor a proper exceptional inverse image
is used. The canonical trace constructed in `Trace.Proper` is the consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The ordinary canonical pullback associated to an invertible actual trace.
Invertibility is a premise here, not a theorem for arbitrary proper maps. -/
def ordinaryTracePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : X.Modules} {N : Y.Modules} (τ : (pushforward f).obj M ⟶ N) [IsIso τ] :
    (pullback f).obj N ⟶ M :=
  ((pullbackPushforwardAdjunction f).homEquiv N M).symm (inv τ)

/-- The defining formula is the actual counit after the pullback of the inverse trace. -/
theorem ordinaryTracePullback_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : X.Modules} {N : Y.Modules} (τ : (pushforward f).obj M ⟶ N) [IsIso τ] :
    ordinaryTracePullback f τ =
      (pullback f).map (inv τ) ≫ (pullbackPushforwardAdjunction f).counit.app M :=
  (pullbackPushforwardAdjunction f).homEquiv_counit N M (inv τ)

/-- Open restriction preserves the original adjunction mate of the inverse trace. -/
theorem ordinaryTracePullback_openRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : X.Modules} {N : Y.Modules} (τ : (pushforward f).obj M ⟶ N) [IsIso τ]
    (U : Y.Opens) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map (ordinaryTracePullback f τ) =
      (Pullback.OpenRestriction.localPullbackIso f U).hom.app N ≫
        ((pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).symm
          ((restrictFunctor U.ι).map (inv τ) ≫
            Pullback.OpenRestriction.restrictedPushforwardMap f U M) :=
  Pullback.OpenRestriction.restrictedAdjoint_eq f U (inv τ)

variable {W X T Y : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ T)
    (f : X ⟶ Y) (j : T ⟶ Y) (h : IsPullback a b f j)

private theorem traceSquareRestrictionMap_eq (M : X.Modules) :
    Adjunction.squareRestrictionMap (pullbackPushforwardAdjunction j)
        (pullbackPushforwardAdjunction a) (cartesianPushforwardSquare a b f j h) M =
      (cartesianBaseChangeMap a b f j h).app M := by
  apply ((pullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [Adjunction.squareRestrictionMap, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  exact cartesianBaseChangeMap_unit a b f j h M

/-- Original pullback-composition comparison obtained from the actual pushforward
square and its four original adjunctions. -/
def ordinaryTracePullbackSquareIso :
    pullback f ⋙ pullback a ≅ pullback j ⋙ pullback b :=
  Adjunction.squareLeftIso (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction b) (pullbackPushforwardAdjunction j)
    (pullbackPushforwardAdjunction a) (cartesianPushforwardSquare a b f j h)

/-- Base change of the inverse-trace adjoint is precisely ordinary evaluation
following the pulled-back inverse trace and the actual base-change mate.
This applies to the local-spectrum square without any finiteness over its
original regular base. -/
theorem ordinaryTracePullback_baseChange
    {M : X.Modules} {N : Y.Modules} (τ : (pushforward f).obj M ⟶ N) [IsIso τ] :
    (pullback a).map (ordinaryTracePullback f τ) =
      (ordinaryTracePullbackSquareIso a b f j h).hom.app N ≫
        (pullback b).map ((pullback j).map (inv τ) ≫
          (cartesianBaseChangeMap a b f j h).app M) ≫
        (pullbackPushforwardAdjunction b).counit.app ((pullback a).obj M) := by
  have he := Adjunction.squareAdjoint_eq (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction b) (pullbackPushforwardAdjunction j)
    (pullbackPushforwardAdjunction a) (cartesianPushforwardSquare a b f j h) (inv τ)
  simpa only [ordinaryTracePullback, ordinaryTracePullbackSquareIso,
    traceSquareRestrictionMap_eq, Adjunction.homEquiv_counit, Category.assoc] using he

end AlgebraicGeometry.Scheme.Modules
