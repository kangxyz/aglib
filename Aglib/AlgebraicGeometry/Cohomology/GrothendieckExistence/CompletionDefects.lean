/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.IndependentQuotientDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefects

/-! # One algebraic defect bound controls every original completion stage

The exceptional ideal and the ideal of completion are independent. The same
single doubled exponent works for all stages of the actual completion map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {M N : X.CoherentSheaf} (f : M ⟶ N)

/-- Completion doubles a single ordinary algebraic defect bound uniformly
in the defining-ideal power, retaining the original coefficient map. -/
theorem completionFunctor_map_defectsKilled (I J : X.IdealSheafData) (t : ℕ)
    (hk : killedByIdealSheaf (J ^ t) (kernel f.hom))
    (hc : killedByIdealSheaf (J ^ t) (cokernel f.hom)) :
    AdicSystem.DefectsKilled J (t * 2) ((completionFunctor X I).map f) := by
  let : M.obj.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (M.property R j).1)
  let : N.obj.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (N.property R j).1)
  intro n
  exact independentQuotient_defectsKilled f.hom J (I ^ n) t hk hc

end AlgebraicGeometry.Scheme.Modules.Coherent
