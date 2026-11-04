/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundleStack

/-! Local rank one of the original quasicoherent module descends along an fpqc map. -/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory

/-- Local rank one descends from the original pullback along a faithfully
flat quasi-compact morphism, without a finite-presentation assumption. -/
theorem isLocallyRankOne_of_fpqc_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] (M : Y.Modules) [M.IsQuasicoherent]
    (hM : Invertible.IsLocallyRankOne X ((pullback f).obj M)) :
    Invertible.IsLocallyRankOne Y M := by
  refine prop_of_mem_fpqcPrecoverage (fun Z N ↦ Invertible.IsLocallyRankOne Z N)
    (fun Z _ _ e h ↦ Invertible.isLocallyRankOne_of_iso Z e h)
    (fun _ _ g N h ↦ Invertible.pullback_locallyRankOne g N h)
    (fun _ _ hR N hN ↦ isLocallyRankOne_of_mem_zariskiTopology hR N hN)
    (fun _ _ φ hφ N hN ↦ isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat φ hφ N hN)
    f.singleton_mem_fpqcPrecoverage M ?_
  rintro _ _ ⟨⟩
  exact hM

end AlgebraicGeometry.Scheme.Modules
