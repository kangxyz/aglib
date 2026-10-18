/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.VanishingProjective

/-! Focused consumer of projective global sections and cohomology base change in the vanishing case
over a Noetherian ring (Nitsure, arXiv:math/0504590v1, the vanishing-case step of the exercise
after Lemma 3.2, p. 15; proof of Theorem 4.3, (B) and (C) for a flat family, the input applied to
each flat `F_{V_i}`, p. 21, over an affine Noetherian base), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent AlgebraicGeometry.Scheme.Cohomology

universe u

example {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type u}
    {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    (∀ q, IsIso (moduleCohomologyBaseChangeMap f σ M q)) ∧
      (let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom X α M 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0)) :=
  ⟨fun q => moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
      e hf hM hflat hvan q σ,
    moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding e hf hM hflat hvan⟩


/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding
