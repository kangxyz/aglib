/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.PointComponentOpenRecovery
public import Aglib.AlgebraicGeometry.Properties.Normal.PointComponentLift
public import Aglib.AlgebraicGeometry.Spec.LocalizationIntegralBaseChange

/-! # Localization of the actual pointed normalization component

The original component is selected by the image of the local source's closed
point. Its literal localization pullback is integral and normal, and retains
both projections of the original local-source map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (B S T : Type u) [CommRing B] [CommRing S] [CommRing T]
  [IsDomain B] [IsNoetherianRing B] [Algebra B S]
  (M : Submonoid B) [IsLocalization M S] (hM : M ≤ nonZeroDivisors B)
  [IsLocalRing T]
  [∀ x : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x)]
  {U E : Scheme.{u}} (j : U ⟶ Spec (.of B)) [IsOpenImmersion j] [Nonempty U]
  (p : E ⟶ U) [IsFinite p] [Etale p]

local notation "q" => genericMap j p
local instance : IsLocallyNoetherian (q).normalization := by
  let : IsFinite (q).fromNormalization := fromNormalization_isFinite j p
  exact LocallyOfFiniteType.isLocallyNoetherian (q).fromNormalization

local notation "C" => normalComponentOpen (Hom.normalization q) (genericMap_normalStalks j p)

include hM in
/-- The actual selected component and its unchanged localization carry the
original local lift, not a separately chosen connected model. -/
theorem exists_pointComponentLocalizationLift
    (a : Spec (.of T) ⟶ (q).normalization) (r : Spec (.of T) ⟶ Spec (.of S))
    (ha : a ≫ (q).fromNormalization = r ≫ Spec.algebraMap B S) :
    let x := a (IsLocalRing.closedPoint T)
    let c := (C x).ι ≫ (q).fromNormalization
    IsIntegral (pullback c (Spec.algebraMap B S)) ∧
    NormalStalks (pullback c (Spec.algebraMap B S)) ∧
    ∃ d : Spec (.of T) ⟶ pullback c (Spec.algebraMap B S),
      d ≫ pullback.fst c (Spec.algebraMap B S) ≫ (C x).ι = a ∧
      d ≫ pullback.snd c (Spec.algebraMap B S) = r ∧
      (pullback.fst c (Spec.algebraMap B S) ≫ (C x).ι)
        (d (IsLocalRing.closedPoint T)) = x := by
  let x := a (IsLocalRing.closedPoint T)
  let c := (C x).ι ≫ (q).fromNormalization
  let : IsDominant c := pointComponent_isDominant j p x
  have hnormal := pointComponent_normalStalks j p x
  have hint := isIntegral_pullback_localization B S M hM c
  have hn := normalStalks_pullback_localization B S M c hnormal
  let aC := normalComponentLift (q).normalization (genericMap_normalStalks j p) x a rfl
  have hC : aC ≫ c = r ≫ Spec.algebraMap B S := by
    dsimp only [c]
    rw [← Category.assoc, normalComponentLift_fac]
    exact ha
  let d := pullback.lift aC r hC
  have hd : d ≫ pullback.fst c (Spec.algebraMap B S) ≫ (C x).ι = a := by
    rw [← Category.assoc, pullback.lift_fst, normalComponentLift_fac]
  refine ⟨hint, hn, d, hd, pullback.lift_snd _ _ _, ?_⟩
  exact congrArg (fun k : Spec (.of T) ⟶ (q).normalization =>
    k (IsLocalRing.closedPoint T)) hd

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
