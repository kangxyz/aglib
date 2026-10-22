/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionBaseStages
public import Aglib.LinearAlgebra.DefectIdealBound

/-! # Finite-stage defect bounds reflect through the original completion unit

Reflection uses bijectivity of the actual unit on coefficients killed by an
ideal power, not faithful flatness of the completion of the base ring.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B] (I : Ideal B)
  {M N : (Spec B).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  [Module.Finite B (moduleSpecΓFunctor.obj M)]
  [Module.Finite B (moduleSpecΓFunctor.obj N)]
  (q : M ⟶ N) (t s : ℕ)
  (hM : I ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)) = ⊥)
  (hN : I ^ s • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) = ⊥)

include t s hM hN in
/-- A bound on the actual pulled map reflects to the original finite-stage map. -/
theorem completionPullback_defectBounds_reflect (J : Ideal B)
    (hk : let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
      J • (moduleSpecΓFunctor.map ((pushforward w).map ((pullback w).map q))).hom.ker = ⊥)
    (hc : let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
      J • (⊤ : Submodule B (moduleSpecΓFunctor.obj
        ((pushforward w).obj ((pullback w).obj N)))) ≤
          (moduleSpecΓFunctor.map ((pushforward w).map ((pullback w).map q))).hom.range) :
    J • (moduleSpecΓFunctor.map q).hom.ker = ⊥ ∧
      J • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) ≤
        (moduleSpecΓFunctor.map q).hom.range := by
  let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
  let e := completionPullbackUnitSectionsEquiv I M t hM
  let d := completionPullbackUnitSectionsEquiv I N s hN
  let f := (moduleSpecΓFunctor.map q).hom
  let g := (moduleSpecΓFunctor.map ((pushforward w).map ((pullback w).map q))).hom
  apply LinearMap.defectBounds_of_equiv g f e.symm d.symm _ J hk hc
  intro x
  apply d.injective
  rw [LinearEquiv.apply_symm_apply]
  have hn := completionPullbackUnitSectionsEquiv_naturality I M N q t s hM hN (e.symm x)
  change g (e (e.symm x)) = d (f (e.symm x)) at hn
  rw [LinearEquiv.apply_symm_apply] at hn
  exact hn.symm

end AlgebraicGeometry.Scheme.Modules.Coherent
