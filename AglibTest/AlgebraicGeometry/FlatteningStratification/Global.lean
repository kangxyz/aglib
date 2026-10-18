/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Global

/-! Focused consumer of Nitsure's flattening stratification over a Noetherian base
(arXiv:math/0504590v1, Thm 4.3, p. 19), for locally Noetherian test schemes, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- **Nitsure's Theorem 4.3 over a Noetherian base** `S` (quasi-compact and locally Noetherian),
for `F` coherent on `P^n_A ×_{Spec A} S` and locally Noetherian test schemes: finitely many fibre
Hilbert polynomials occur; the strata `S_f` are immersions with `|S_f| = {y : P_y = f}` (i);
`∐ S_f ⟶ S` is a monomorphism representing flatness of the pullback of `F` (ii); and the closure
of `|S_f|` lies in the union of the `|S_g|`, `g ≥ f` (iii). -/
example {A : Type u} [CommRing A] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) {S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S] (s : S ⟶ Spec (CommRingCat.of A))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (pullback (toSpec A ι) s) F) :
    (Set.range (Scheme.Cohomology.fiberHilbertPolynomialAt ι s F)).Finite ∧
      (∀ f : Polynomial ℚ, IsImmersion (Scheme.Cohomology.flatteningStratumι ι s n e hF f) ∧
        Set.range (Scheme.Cohomology.flatteningStratumι ι s n e hF f) =
          {y | Scheme.Cohomology.fiberHilbertPolynomialAt ι s F y = f}) ∧
      Mono (Scheme.Cohomology.flatteningStrataι ι s n e hF) ∧
      (∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ S),
        (∃ h : T ⟶ Scheme.Cohomology.flatteningStrata ι s n e hF,
            h ≫ Scheme.Cohomology.flatteningStrataι ι s n e hF = g) ↔
          Scheme.Modules.relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F)) ∧
      ∀ f : Polynomial ℚ, closure (Set.range (Scheme.Cohomology.flatteningStratumι ι s n e hF f)) ⊆
        ⋃ g ∈ {g ∈ Set.range (Scheme.Cohomology.fiberHilbertPolynomialAt ι s F) |
            ∀ᶠ m : ℕ in Filter.atTop, f.eval (m : ℚ) ≤ g.eval (m : ℚ)},
          Set.range (Scheme.Cohomology.flatteningStratumι ι s n e hF g) :=
  ⟨Scheme.Cohomology.finite_range_fiberHilbertPolynomialAt ι s n e hF,
    fun f => ⟨inferInstance, Scheme.Cohomology.range_flatteningStratumι ι s n e hF f⟩,
    Scheme.Cohomology.mono_flatteningStrataι ι s n e hF,
    fun _ _ g => Scheme.Cohomology.exists_lift_flatteningStrataι_iff ι s n e hF g,
    Scheme.Cohomology.closure_range_flatteningStratumι_subset ι s n e hF⟩

/-- The universal property of one stratum: flatness with all fibre Hilbert polynomials `f`. -/
example {A : Type u} [CommRing A] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) {S : Scheme.{u}}
    [IsLocallyNoetherian S] (s : S ⟶ Spec (CommRingCat.of A))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (pullback (toSpec A ι) s) F)
    (f : Polynomial ℚ) {T : Scheme.{u}} [IsLocallyNoetherian T] (g : T ⟶ S) :
    (∃ h : T ⟶ Scheme.Cohomology.flatteningStratum ι s n e hF f,
        h ≫ Scheme.Cohomology.flatteningStratumι ι s n e hF f = g) ↔
      Scheme.Modules.relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) ∧
        ∀ t : T, Scheme.Cohomology.fiberHilbertPolynomialAt ι s F (g t) = f :=
  Scheme.Cohomology.exists_lift_flatteningStratumι_iff ι s n e hF f g


/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_isImmersion_flatteningStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_isImmersion_flatteningStratum

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_flatteningStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_flatteningStratum

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_iso_flatteningStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_iso_flatteningStratum

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.range_flatteningStratumι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.range_flatteningStratumι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.iUnion_range_flatteningStratumι_eq_univ_and_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.iUnion_range_flatteningStratumι_eq_univ_and_pairwiseDisjoint

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.mono_flatteningStrataι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.mono_flatteningStrataι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_exists_lift_flatteningStrataι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_of_exists_lift_flatteningStrataι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStrataι_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStrataι_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStrataι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStrataι_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_flatteningStrata' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_flatteningStrata

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.closure_range_flatteningStratumι_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.closure_range_flatteningStratumι_subset

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_iso_pullback_flatteningStratumι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_iso_pullback_flatteningStratumι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isLocallyNoetherian_flatteningStrata' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isLocallyNoetherian_flatteningStrata

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStratumι_iff_pullbackBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStratumι_iff_pullbackBaseChange

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStrataι_iff_pullbackBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_flatteningStrataι_iff_pullbackBaseChange
