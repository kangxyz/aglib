/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fpqc.LineBundle
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteType

/-! Effective Cartierness of the original closed immersion descends fpqc. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- On the actual Cartesian square of a closed immersion, fpqc descent
of the original ideal's local rank one gives effective Cartierness. -/
theorem isEffectiveCartier_of_fpqc_pullback {D X D' X' : Scheme.{u}}
    (i : D ⟶ X) (j : D' ⟶ X') (a : D' ⟶ D) (b : X' ⟶ X)
    (h : IsPullback a j i b) [IsClosedImmersion i]
    [Flat b] [Surjective b] [QuasiCompact b] (hj : IsEffectiveCartier j) :
    IsEffectiveCartier i := by
  let : IsIso (idealPullbackMap i j b a h.w) :=
    idealPullbackMap_isIso_of_flat i b j a h.w h
  let : (idealModule i).IsQuasicoherent := idealModule_isQuasicoherent i
  exact ⟨inferInstance, isLocallyRankOne_of_fpqc_pullback b (idealModule i)
    (isLocallyRankOne_of_iso X' (asIso (idealPullbackMap i j b a h.w)).symm
      hj.isLocallyRankOne)⟩

end AlgebraicGeometry.Scheme.Hom
