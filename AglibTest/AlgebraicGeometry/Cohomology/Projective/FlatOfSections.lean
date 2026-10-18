/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FlatOfSections

/-! Focused consumer of Nitsure's Lemma 3.2 over an affine base (arXiv:math/0504590v1, p. 15):
flatness from flat or projective global sections of large twists, and the equivalence with the
converse for coherent modules over a Noetherian ring, with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Lemma 3.2: projective global sections of all large twists give relative flatness. -/
example {R : Type u} [CommRing R] {ι : Type u} [Finite ι] (F : (ProjectiveSpace R ι).Modules)
    [F.IsQuasicoherent] (N : ℤ)
    (hproj : ∀ d : ℤ, N ≤ d →
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0))) :
    relativeFlat (toSpec R ι) F :=
  relativeFlat_of_projective_twistedSections F N hproj

/-- Over a field every quasicoherent module on projective space is relatively flat, since every
vector space is flat. -/
example {K : Type u} [Field K] {ι : Type u} [Finite ι] (F : (ProjectiveSpace K ι).Modules)
    [F.IsQuasicoherent] : relativeFlat (toSpec K ι) F :=
  relativeFlat_of_flat_twistedSections F 0 fun _ _ => by
    intro α
    infer_instance

/-- Lemma 3.2 with its converse, for coherent modules over a Noetherian ring. -/
example {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    relativeFlat (toSpec R ι) F ↔ ∃ N : ℤ, ∀ d : ℤ, N ≤ d →
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0)) :=
  relativeFlat_iff_exists_projective_twistedSections n e F hF

/--
info: 'AlgebraicGeometry.Scheme.Modules.unitHomGlobalSectionsLinearEquivOfHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.unitHomGlobalSectionsLinearEquivOfHom

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistHomLinearEquivH0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistHomLinearEquivH0

/--
info: 'AlgebraicGeometry.ProjectiveSpace.flat_coordinateOpen_sections_of_flat_negativeTwistHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.flat_coordinateOpen_sections_of_flat_negativeTwistHom

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_flat_twistedSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_flat_twistedSections

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_projective_twistedSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_projective_twistedSections

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_iff_exists_projective_twistedSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_iff_exists_projective_twistedSections
