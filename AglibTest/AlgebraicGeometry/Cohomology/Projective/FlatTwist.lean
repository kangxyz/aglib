/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FlatTwist

/-! Focused consumer of the direct images of large twists of a flat family over a Noetherian ring,
and over a Noetherian local ring (Nitsure, arXiv:math/0504590v1, exercise after Lemma 3.2, p. 15;
proof of Theorem 4.3, (B) and (C) for a flat family, the input applied to each flat `F_{V_i}`,
p. 21, over an affine Noetherian base), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

/-- The global sections of a large twist of a flat family over a Noetherian ring are projective and
commute with every base change. -/
example {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (hflat : relativeFlat (toSpec R ι) F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      (∀ (q : ℕ) (B' : Type u) [CommRing B'] (σ : R →+* B'),
        IsIso (moduleCohomologyBaseChangeMap (toSpec R ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) q)) ∧
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0)) :=
  exists_twist_baseChange_isIso_and_projective_of_relativeFlat n e F hF hflat

/-- Over a Noetherian local ring the global sections are free. -/
example {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (hflat : relativeFlat (toSpec R ι) F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      (∀ (q : ℕ) (B' : Type u) [CommRing B'] (σ : R →+* B'),
        IsIso (moduleCohomologyBaseChangeMap (toSpec R ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) q)) ∧
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0)) :=
  exists_twist_baseChange_isIso_and_free_of_relativeFlat n e F hF hflat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_isIso_and_free_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_isIso_and_free_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_isIso_and_projective_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_baseChange_isIso_and_projective_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_twist_subsingleton_cohomology_pullback_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_twist_subsingleton_cohomology_pullback_of_relativeFlat
