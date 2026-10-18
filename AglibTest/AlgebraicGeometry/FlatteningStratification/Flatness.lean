/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Flatness

/-! Focused consumer of the universal property of the flattening stratification (Nitsure,
arXiv:math/0504590v1, Thm 4.3 (ii), proof pp. 22–23) over an affine Noetherian base, with axiom
guards for it and for the new helper leaves it uses. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- Theorem 4.3 (ii) with the bound of the fibre statements of (B) and (C): there is `N` such that,
for every locally Noetherian `T`, a morphism `g : T ⟶ Spec A` factors through `∐ S_f ⟶ Spec A`, a
monomorphism, exactly when the pullback of `F` to `P^n_A ×_{Spec A} T` is flat over `T`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F) :
    ∃ N : ℕ, Mono (Scheme.Cohomology.hilbertPolynomialStrataι n e F hF N) ∧
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ Spec (CommRingCat.of A)),
        (∃ h : T ⟶ Scheme.Cohomology.hilbertPolynomialStrata n e F hF N,
            h ≫ Scheme.Cohomology.hilbertPolynomialStrataι n e F hF N = g) ↔
          Scheme.Modules.relativeFlat (pullback.snd (toSpec A ι) g)
            ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj F) := by
  obtain ⟨N, hN⟩ := Scheme.Cohomology.exists_isFiberBaseChangeBound n e F hF
  exact ⟨N, Scheme.Cohomology.mono_hilbertPolynomialStrataι n e F hF hN, fun T _ g =>
    Scheme.Cohomology.exists_lift_hilbertPolynomialStrataι_iff n e F hF hN g⟩

/-- The direction "⇒" for an arbitrary test scheme, and flatness over `∐ S_f` itself. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F) {N : ℕ}
    (hN : Scheme.Cohomology.IsFiberBaseChangeBound F N) {T : Scheme.{u}}
    (h : T ⟶ Scheme.Cohomology.hilbertPolynomialStrata n e F hF N) :
    Scheme.Modules.relativeFlat
      (pullback.snd (toSpec A ι) (h ≫ Scheme.Cohomology.hilbertPolynomialStrataι n e F hF N))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (h ≫ Scheme.Cohomology.hilbertPolynomialStrataι n e F hF N))).obj F) :=
  Scheme.Cohomology.relativeFlat_of_exists_lift_hilbertPolynomialStrataι n e F hF hN _ h rfl

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStrataι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStrataι_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_exists_lift_hilbertPolynomialStrataι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_exists_lift_hilbertPolynomialStrataι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStrataι_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStrataι_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.mono_hilbertPolynomialStrataι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.mono_hilbertPolynomialStrataι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_hilbertPolynomialStrata' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_hilbertPolynomialStrata

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_hilbertPolynomialStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_hilbertPolynomialStratum

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_iso_hilbertPolynomialStrata' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_iso_hilbertPolynomialStrata

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isLocallyNoetherian_hilbertPolynomialStrata' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isLocallyNoetherian_hilbertPolynomialStrata

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.sigmaι_hilbertPolynomialStrataι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.sigmaι_hilbertPolynomialStrataι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isFiniteLocallyFree_pullback_directImageTwist_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isFiniteLocallyFree_pullback_directImageTwist_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_map_of_isFiniteLocallyFree_pullback_directImageTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.relativeFlat_map_of_isFiniteLocallyFree_pullback_directImageTwist

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_isFiberBaseChangeBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_isFiberBaseChangeBound

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat_pullback

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.directImageTwistSectionsLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.directImageTwistSectionsLinearEquiv

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistCohomologyLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeTwistCohomologyLinearEquiv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.baseChangeIso_hom_appTop_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.baseChangeIso_hom_appTop_comp

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyMapAlongLinearOfEq_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyMapAlongLinearOfEq_apply

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullbackLinearOfEq_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullbackLinearOfEq_apply

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_of_isPullback_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_of_isPullback_comp

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_of_isPullback_of_forall_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_of_isPullback_of_forall_exists

/--
info: 'AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_specMap_iff_projective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_specMap_iff_projective

/--
info: 'AlgebraicGeometry.Scheme.exists_lift_of_mono_of_forall_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.exists_lift_of_mono_of_forall_exists

/--
info: 'AlgebraicGeometry.Scheme.mono_sigmaDesc_of_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.mono_sigmaDesc_of_pairwise_disjoint
