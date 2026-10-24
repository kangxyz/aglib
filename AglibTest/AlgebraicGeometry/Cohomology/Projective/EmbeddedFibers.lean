/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Family
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Monotone
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Twist

/-! Focused consumer of twisted cohomology on the fibres of a projective embedding: the bridge to
`P^N_K`, the polynomial Euler characteristic, the finite reduction of the vanishing condition,
Serre vanishing, sections of large twists, monotonicity of `h^0`, the twist shift, and the
family statements, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))

/-- **The bridge** to `P^N_K`, and the Hilbert polynomial of the fibre. -/
example (N : ℕ) (e : ι ≃ Fin (N + 1)) (M : (pullback (i ≫ toSpec A ι) k).Modules)
    (hM : affineLocallyFiniteType _ M) (n : ℤ) (q : ℕ) :
    embeddedFiberTwistDim i k M n q =
        projectiveCohomologyDim K ι ((moduleTensorLeftFunctor (ProjectiveSpace K ι)
          (twistingSheaf K ι n)).obj ((pushforward (embeddedFiberι i k)).obj M)) q ∧
      ∃ φ : Polynomial ℚ, ∀ n : ℤ,
        (embeddedFiberTwistEulerChar i k M n : ℚ) = φ.eval (n : ℚ) :=
  ⟨embeddedFiberTwistDim_eq_projectiveCohomologyDim i k M hM n q,
    exists_embeddedFiberTwistEulerChar_eq_eval i k N e M hM⟩

/-- **Finitely many vanishing conditions**, Serre vanishing and sections of large twists. -/
example (N : ℕ) (e : ι ≃ Fin (N + 1)) (M : (pullback (i ≫ toSpec A ι) k).Modules)
    (hM : affineLocallyFiniteType _ M) (hM0 : ¬ IsZero M) (m : ℤ) :
    ((∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n → embeddedFiberTwistDim i k M n q = 0) ↔
      (∀ q : ℕ, 0 < q → q ≤ N → ∀ n : ℤ, m ≤ n → n < m + N →
        embeddedFiberTwistDim i k M n q = 0)) ∧
    (∃ B : ℤ, ∀ n : ℤ, B ≤ n → ∀ q : ℕ, 0 < q → embeddedFiberTwistDim i k M n q = 0) ∧
    (∃ B : ℤ, ∀ n : ℤ, B ≤ n → embeddedFiberTwistDim i k M n 0 ≠ 0) :=
  ⟨embeddedFiberTwistDim_vanishing_iff i k N e M hM m,
    exists_embeddedFiberTwistDim_eq_zero i k N e M hM,
    exists_embeddedFiberTwistDim_zero_ne_zero i k N e M hM hM0⟩

/-- **Monotonicity of `h^0`** for a line bundle on the fibre, and the **twist shift**. -/
example (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) k)) {m m' : ℤ} (h : m ≤ m') (n : ℤ)
    (q : ℕ) :
    embeddedFiberTwistDim i k L.val m 0 ≤ embeddedFiberTwistDim i k L.val m' 0 ∧
      embeddedFiberTwistDim i k (pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) m L.val) n q =
        embeddedFiberTwistDim i k L.val (n + m) q :=
  ⟨embeddedFiberTwistDim_zero_mono i N e k L h,
    embeddedFiberTwistDim_pulledTwist i k L.val
      (affineLocallyFiniteType_of_isLocallyRankOne L.property) m n q⟩

/-- **The family statements**: semicontinuity, local constancy, and openness of the vanishing
locus on a locally Noetherian `T`. -/
example [Finite ι] [Flat (i ≫ toSpec A ι)] {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A)) (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) g))
    (N : ℕ) (e : ι ≃ Fin (N + 1)) (m n : ℤ) (q : ℕ) :
    UpperSemicontinuous (fun t : T => embeddedFiberTwistDim i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q) ∧
    IsLocallyConstant (fun t : T => embeddedFiberTwistEulerChar i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n) ∧
    IsOpen {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0} :=
  ⟨upperSemicontinuous_embeddedFiberTwistDim i g L n q,
    isLocallyConstant_embeddedFiberTwistEulerChar i g L n,
    isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero i g L N e m⟩

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.embeddedFiberTwistDim_eq_projectiveCohomologyDim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embeddedFiberTwistDim_eq_projectiveCohomologyDim

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.embeddedFiberTwistDim_vanishing_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embeddedFiberTwistDim_vanishing_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.embeddedFiberTwistDim_zero_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embeddedFiberTwistDim_zero_mono

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.embeddedFiberTwistDim_pulledTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embeddedFiberTwistDim_pulledTwist
