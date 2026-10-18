/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LargeTwistBaseChange

/-! Focused consumer of the base change of global sections of large twists without flatness
(Nitsure, arXiv:math/0504590v1, Lemma 3.1, p. 13, over affine Noetherian `S` and `T`), with axiom
guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Nitsure's statement for `S = Spec A`, `T = Spec B`: the base-change homomorphism of global
sections of `F(r)` is an isomorphism for all `r ≥ r₀`, where `r₀` depends on `σ`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B) :
    ∃ r₀ : ℤ, ∀ r : ℤ, r₀ ≤ r →
      IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι r)).obj F) 0) := by
  obtain ⟨N, hN⟩ := exists_twist_baseChange_isIso_of_isNoetherianRing n e F hF σ
  exact ⟨N, fun r hr => (hN r hr).2.2⟩

/-- The same bound gives the vanishing of the positive cohomology of `F(r)` and of its pullback
to the fibre product. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) q)) ∧
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q)) :=
  let ⟨N, hN⟩ := exists_twist_baseChange_isIso_of_isNoetherianRing n e F hF σ
  ⟨N, fun d hd => ⟨(hN d hd).1, (hN d hd).2.1⟩⟩

/-- The form with `𝒪_B(r) ⊗ π^* F` on `P^n_B`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      Function.Bijective (baseChangeTwistCohomologyHom σ ι d F 0 ∘
        moduleCohomologyBaseChangeMap (toSpec A ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) :=
  exists_twist_baseChange_bijective_projectiveSpace n e F hF σ

/--
info: 'ModuleCat.extendScalars_map_exact_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.extendScalars_map_exact_of_surjective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_H0_exact_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_H0_exact_of_exact

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistIso_hom_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistIso_hom_naturality

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.bijective_sheafH_map_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.bijective_sheafH_map_of_iso

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistCohomologyHom_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistCohomologyHom_bijective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistCohomologyHom_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistCohomologyHom_naturality

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeMap_twist_isIso_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeMap_twist_isIso_of_exact

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_isIso_of_isNoetherianRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_isIso_of_isNoetherianRing

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_bijective_projectiveSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_bijective_projectiveSpace
