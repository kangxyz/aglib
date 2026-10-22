/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedBaseChange
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Sections

/-! # Original completion-base units on bounded affine stages

The actual geometric pullback unit is bijective on original affine sections
for finite coefficients annihilated by an ideal power. No faithful-flatness
claim is made for arbitrary coefficients. Targets retain the original
pushforward scalar structure, so these are genuine original-ring comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B] (I : Ideal B)
  (M : (Spec B).Modules) [M.IsQuasicoherent]
  [Module.Finite B (moduleSpecΓFunctor.obj M)]

/-- The actual geometric unit is bijective on a bounded coherent affine stage. -/
theorem completionPullbackUnit_sections_bijective (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)) = ⊥) :
    Function.Bijective (moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B))))).unit.app M)) := by
  let φ : B ⟶ CommRingCat.of (AdicCompletion I B) :=
    CommRingCat.ofHom (algebraMap B (AdicCompletion I B))
  have hmodule : Module.compHom (AdicCompletion I B) (algebraMap B (AdicCompletion I B)) =
      (inferInstance : Module B (AdicCompletion I B)) := by
    apply Module.ext
    funext r x
    exact (Algebra.smul_def r x).symm
  have ht : Function.Bijective (fun m : moduleSpecΓFunctor.obj M =>
      (1 : AdicCompletion I B) ⊗ₜ[B,φ.hom] m) := by
    change Function.Bijective (fun m : moduleSpecΓFunctor.obj M =>
      (1 : AdicCompletion I B) ⊗ₜ[B,algebraMap B (AdicCompletion I B)] m)
    rw [hmodule]
    exact AdicCompletion.one_tmul_bijective_of_pow_killed I (moduleSpecΓFunctor.obj M) t hM
  have hu : (fun m : moduleSpecΓFunctor.obj M =>
      moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) m) =
      (fun z => (affinePullbackGlobalSectionsIso φ M).hom z) ∘
        (fun m => (1 : AdicCompletion I B) ⊗ₜ[B,φ.hom] m) := by
    funext m
    exact (affinePullbackGlobalSectionsIso_one_tmul φ M m).symm
  change Function.Bijective (fun m : moduleSpecΓFunctor.obj M =>
    moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) m)
  rw [hu]
  exact (ConcreteCategory.bijective_of_isIso (affinePullbackGlobalSectionsIso φ M).hom).comp ht

/-- This original-ring equivalence is precisely the original geometric unit. -/
def completionPullbackUnitSectionsEquiv (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)) = ⊥) :
    moduleSpecΓFunctor.obj M ≃ₗ[B]
      moduleSpecΓFunctor.obj ((pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B))))).obj
          ((pullback (Spec.map (CommRingCat.ofHom
            (algebraMap B (AdicCompletion I B))))).obj M)) :=
  LinearEquiv.ofBijective
    (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B))))).unit.app M)).hom
    (completionPullbackUnit_sections_bijective I M t hM)

/-- Original stage maps commute with these original-ring equivalences. -/
theorem completionPullbackUnitSectionsEquiv_naturality
    (N : (Spec B).Modules) [N.IsQuasicoherent]
    [Module.Finite B (moduleSpecΓFunctor.obj N)]
    (q : M ⟶ N) (t s : ℕ)
    (hM : I ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)) = ⊥)
    (hN : I ^ s • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) = ⊥)
    (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B))))).map
        ((pullback (Spec.map (CommRingCat.ofHom
          (algebraMap B (AdicCompletion I B))))).map q))
      (completionPullbackUnitSectionsEquiv I M t hM x) =
    completionPullbackUnitSectionsEquiv I N s hN (moduleSpecΓFunctor.map q x) := by
  let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
  have h := congrArg (fun k => moduleSpecΓFunctor.map k x)
    ((pullbackPushforwardAdjunction w).unit.naturality q)
  change moduleSpecΓFunctor.map ((pushforward w).map ((pullback w).map q))
      (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction w).unit.app M) x) =
    moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction w).unit.app N)
      (moduleSpecΓFunctor.map q x)
  simpa only [Functor.map_comp, Functor.comp_map, Functor.id_map,
    ConcreteCategory.comp_apply] using h.symm

end AlgebraicGeometry.Scheme.Modules.Coherent
