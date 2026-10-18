/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.VanishingBaseChange

/-! Focused consumer of cohomology and base change in the vanishing case (Nitsure,
arXiv:math/0504590v1, proof of Theorem 4.3, (B) and (C) for a flat family, the input applied to
each flat `F_{V_i}`, p. 21, over an affine Noetherian base), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Over a Noetherian local ring, vanishing of positive-degree cohomology makes every residue-field
base-change map surjective and global sections free. -/
example {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {ι : Type u}
    {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := Scheme.Cohomology.moduleCohomologyModuleOfHom X α M 0
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :=
  Scheme.Cohomology.moduleCohomology_zero_free_of_vanishing_of_projectiveEmbedding
    e hf hM hflat hvan

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel.epi_residue_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel.epi_residue_of_vanishing

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_zero_free_of_vanishing_of_projectiveEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_zero_free_of_vanishing_of_projectiveEmbedding
