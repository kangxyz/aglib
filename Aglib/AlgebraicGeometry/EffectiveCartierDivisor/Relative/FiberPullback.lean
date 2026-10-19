/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic

/-!
# Pullbacks of the ideal to maps into fibres

For `p : X ⟶ T`, a module `M` on `X` and a set `Z` of points of `T`,
`Scheme.Hom.FiberPullbackRankOne p M Z` says that `M` pulls back to a locally rank-one module
along every morphism `g : Y ⟶ X` whose composite with `p` factors through
`Spec κ(t) ⟶ T` for some `t ∈ Z`. If `D ⊆ X` is closed and flat over `T` and every fibre
`D_t ⊆ X_t`, `t ∈ Z`, is an effective Cartier divisor, the actual ideal of `D` has this
property (`fiberPullbackRankOne_idealModule`): such a `g` factors through the fibre `X_t`, and
flatness identifies the pullback of the ideal to `X_t` with the ideal of `D_t`.

The property transports along morphisms of families and isomorphisms of modules, and it gives
local rank one along every field-valued point over `Z`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

variable {D X T : Scheme.{u}}

/-- The module `M` on `X` pulls back to a locally rank-one module along every morphism into a
fibre of `p` over a point of `Z`. -/
def FiberPullbackRankOne (p : X ⟶ T) (M : X.Modules) (Z : Set T) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ X) (t : T), t ∈ Z → ∀ (k : Y ⟶ Spec (T.residueField t)),
    g ≫ p = k ≫ T.fromSpecResidueField t →
      IsLocallyRankOne Y ((Scheme.Modules.pullback g).obj M)

/-- The ideal of a closed subscheme flat over the base pulls back to a locally rank-one module
along every morphism into a fibre whose fibre divisor is effective Cartier. -/
theorem fiberPullbackRankOne_idealModule (p : X ⟶ T) (i : D ⟶ X) [IsClosedImmersion i]
    [Flat (i ≫ p)] (Z : Set T) (hZ : ∀ t ∈ Z, FiberIsEffectiveCartier i p t) :
    FiberPullbackRankOne p (idealModule i) Z := by
  intro Y g t ht k hk
  let q := T.fromSpecResidueField t
  let j : Y ⟶ pullback p q := pullback.lift g k hk
  have hj : j ≫ pullback.fst p q = g := pullback.lift_fst _ _ _
  have : IsIso (idealPullbackMap i (fibreInclusion p i q) (pullback.fst p q)
      (pullback.fst (i ≫ p) q) (fibreInclusion_fst p i q).symm) :=
    flatQuotient_idealPullbackMap_isIso p q (pullback.snd p q) (pullback.fst p q) i
      (fibreInclusion p i q) _ _ (IsPullback.of_hasPullback p q) (fibreInclusion_isPullback p i q)
  have hfib : IsLocallyRankOne (pullback p q)
      ((Scheme.Modules.pullback (pullback.fst p q)).obj (idealModule i)) :=
    isLocallyRankOne_of_iso _ (asIso (idealPullbackMap i (fibreInclusion p i q)
      (pullback.fst p q) (pullback.fst (i ≫ p) q) (fibreInclusion_fst p i q).symm)).symm
      (hZ t ht).isLocallyRankOne
  exact isLocallyRankOne_of_iso _
    (((Scheme.Modules.pullbackComp j (pullback.fst p q)).app (idealModule i)) ≪≫
      (Scheme.Modules.pullbackCongr hj).app (idealModule i))
    (pullback_locallyRankOne j _ hfib)

/-- The fibre pullback condition is invariant under isomorphisms of modules. -/
theorem FiberPullbackRankOne.of_iso {p : X ⟶ T} {M N : X.Modules} {Z : Set T}
    (hM : FiberPullbackRankOne p M Z) (e : M ≅ N) : FiberPullbackRankOne p N Z := by
  intro Y g t ht k hk
  exact isLocallyRankOne_of_iso _ ((Scheme.Modules.pullback g).mapIso e) (hM Y g t ht k hk)

/-- The fibre pullback condition transports along a morphism of families. -/
theorem FiberPullbackRankOne.pullback {X' T' : Scheme.{u}} {p : X ⟶ T} {M : X.Modules}
    {Z : Set T} (hM : FiberPullbackRankOne p M Z) (h : X' ⟶ X) (p' : X' ⟶ T') (m : T' ⟶ T)
    (w : h ≫ p = p' ≫ m) :
    FiberPullbackRankOne p' ((Scheme.Modules.pullback h).obj M) (m ⁻¹' Z) := by
  intro Y g t ht k hk
  have hk' : (g ≫ h) ≫ p = (k ≫ Spec.map (m.residueFieldMap t)) ≫
      T.fromSpecResidueField (m t) := by
    rw [Category.assoc, w, ← Category.assoc, hk, Category.assoc, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  exact isLocallyRankOne_of_iso _ ((Scheme.Modules.pullbackComp g h).app M).symm
    (hM Y (g ≫ h) (m t) ht _ hk')

/-- Along a field-valued point lying over `Z`, the module pulls back to a line. -/
theorem FiberPullbackRankOne.fieldPoint {p : X ⟶ T} {M : X.Modules} {Z : Set T}
    (hM : FiberPullbackRankOne p M Z) (K : Type u) [Field K] (f : Spec (.of K) ⟶ X)
    (hf : p (f (IsLocalRing.closedPoint K)) ∈ Z) :
    IsLocallyRankOne (Spec (.of K)) ((Scheme.Modules.pullback f).obj M) :=
  hM _ f _ hf _ (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K T (f ≫ p)).symm

/-- A morphism whose composite with `p` factors through a field-valued point over `Z` pulls the
module back to a locally rank-one module. -/
theorem FiberPullbackRankOne.of_comp_eq {p : X ⟶ T} {M : X.Modules} {Z : Set T}
    (hM : FiberPullbackRankOne p M Z) {Y : Scheme.{u}} (g : Y ⟶ X) (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ T) (hf : f (IsLocalRing.closedPoint K) ∈ Z) (k : Y ⟶ Spec (.of K))
    (hg : g ≫ p = k ≫ f) : IsLocallyRankOne Y ((Scheme.Modules.pullback g).obj M) := by
  refine hM Y g _ hf (k ≫ Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo f))) ?_
  rw [hg, Category.assoc, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]

end AlgebraicGeometry.Scheme.Hom
