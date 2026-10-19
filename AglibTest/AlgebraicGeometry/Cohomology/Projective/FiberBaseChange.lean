/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiberBaseChange

/-! Focused consumer of statements (B) and (C) for a coherent sheaf that need not be flat (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, p. 21), with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- (C): one bound gives, at every point `s`, vanishing of the positive fibre cohomology and
bijectivity of `κ(s) ⊗ H^0(F(d)) ⟶ H^0(P^n_s, F_s(d))`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d → ∀ s : PrimeSpectrum A,
      Function.Bijective (Scheme.Cohomology.moduleCohomologyBaseChangeMap (toSpec A ι)
        (algebraMap A s.asIdeal.ResidueField)
        ((Scheme.Modules.moduleTensorLeftFunctor (ProjectiveSpace A ι)
          (twistingSheaf A ι d)).obj F) 0) := by
  obtain ⟨N, hN⟩ := Scheme.Cohomology.exists_twist_vanishing_and_fiber_baseChange_isIso n e F hF
  refine ⟨N, fun d hd s => ?_⟩
  have := (hN d hd).2.2 s
  exact ConcreteCategory.bijective_of_isIso _

/-- With the comparison of `BaseChangeComparison`, (B) and (C) make the base change of large twists
to any Noetherian `B` over which `F` becomes flat bijective (the converse half of Thm 4.3 (ii),
p. 22, over affine bases). -/
example {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsNoetherianRing B]
    (σ : A →+* B) {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F)
    (hflat : Scheme.Modules.relativeFlat (toSpec B ι)
      ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      Function.Bijective (Scheme.Cohomology.baseChangeTwistCohomologyHom σ ι d F 0 ∘
        Scheme.Cohomology.moduleCohomologyBaseChangeMap (toSpec A ι) σ
          ((Scheme.Modules.moduleTensorLeftFunctor (ProjectiveSpace A ι)
            (twistingSheaf A ι d)).obj F) 0) := by
  have h := Scheme.Cohomology.exists_twist_fiber_vanishing_and_bijective_projectiveSpace n e F hF
  rcases h with ⟨N, hN⟩
  exact ⟨N, fun d hd =>
    (Scheme.Cohomology.bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace σ n e F
      hF d (fun s => (hN d hd s).2) (fun s q hq => (hN d hd s).1 q hq) hflat).1⟩

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_fiber_vanishing_and_bijective_projectiveSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.exists_twist_fiber_vanishing_and_bijective_projectiveSpace

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_vanishing_and_fiber_baseChange_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_vanishing_and_fiber_baseChange_isIso

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_vanishing_and_fiber_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_vanishing_and_fiber_vanishing

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_fiber_baseChange_of_relativeFlat_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_fiber_baseChange_of_relativeFlat_map

/--
info: 'TopologicalSpace.NoetherianSpace.exists_forall_le_of_isIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.NoetherianSpace.exists_forall_le_of_isIrreducible
