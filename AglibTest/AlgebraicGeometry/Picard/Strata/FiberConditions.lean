/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Strata.FiberConditions

/-! Focused consumer of the fibre conditions defining the strata `Pic^φ` and `Pic^φ_m` of the
Picard functor (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–30, with the plan's
repairs): invariance under isomorphism and base change, openness on locally Noetherian test
schemes, monotonicity, cover, the twist `L ↦ L(m)` and the twisting classes, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of A))

/-- The condition `C_φ` is Kleiman's (4.8.1): `χ(X_t, L_t^{-1}(n)) = φ(n)` for all `n`, with the
actual dual line bundle and `O(n)` pulled back from `P^N_A`. -/
example (φ : ℚ[X]) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    HasFiberDualEulerPolynomial i s φ L t ↔ ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ s)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj
          (dualLineBundle _ L).val) n : ℚ) = φ.eval (n : ℚ) :=
  Iff.rfl

/-- The condition `C_m` is one condition: vanishing (4.8.3) and nonvanishing of `H^0`. -/
example (m : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    HasFiberTwistVanishingAndSections i s m L t ↔
      (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n → fiberTwistDim i s L t n q = 0) ∧
        fiberTwistDim i s L t m 0 ≠ 0 :=
  Iff.rfl

/-- On the fibre, `h^q = 0` is the vanishing of the cohomology group. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (n : ℤ) (q : ℕ) :
    fiberTwistDim i s L t n q = 0 ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _
        (pulledTwist (pullback.fst (i ≫ toSpec A ι) (T.fromSpecResidueField t ≫ s) ≫ i) n
          ((Scheme.Modules.pullback
            (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj L.val))) q) :=
  fiberTwistDim_eq_zero_iff i s N e L t n q

/-- **Isomorphism invariance** of the conditions. -/
example {L L' : LineBundle (pullback (i ≫ toSpec A ι) s)} (e : L.val ≅ L'.val) (t : T)
    (φ : ℚ[X]) (m : ℤ) :
    (HasFiberDualEulerPolynomial i s φ L t ↔ HasFiberDualEulerPolynomial i s φ L' t) ∧
      (HasFiberTwistVanishingAndSections i s m L t ↔
        HasFiberTwistVanishingAndSections i s m L' t) :=
  ⟨hasFiberDualEulerPolynomial_congr i s e t φ, hasFiberTwistVanishingAndSections_congr i s e t m⟩

/-- **Base-change invariance** (`holds_map`): for `b : T' ⟶ T` over `Spec A`, the conditions hold
for `b^* L` at `t'` exactly when they hold for `L` at `b t'`; the dimensions agree. -/
example [IsProper (i ≫ toSpec A ι)] {T' : Scheme.{u}} (s' : T' ⟶ Spec (CommRingCat.of A))
    (b : T' ⟶ T) (hb : b ≫ s = s') (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t' : T')
    (φ : ℚ[X]) (m n : ℤ) (q : ℕ) :
    fiberTwistDim i s' (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t'
        n q = fiberTwistDim i s L (b t') n q ∧
      (HasFiberDualEulerPolynomial i s' φ
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
        HasFiberDualEulerPolynomial i s φ L (b t')) ∧
      (HasFiberTwistVanishingAndSections i s' m
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
        HasFiberTwistVanishingAndSections i s m L (b t')) :=
  ⟨fiberTwistDim_familyBaseChange i s s' b hb L t' n q,
    hasFiberDualEulerPolynomial_pullback_iff i s s' b hb L t' φ,
    hasFiberTwistVanishingAndSections_pullback_iff i s s' b hb L t' m⟩

/-- The base-change map is the map of the Picard functor's family. -/
example {T₁ T₂ : Over (Spec (CommRingCat.of A))} (g : T₂ ⟶ T₁) :
    familyBaseChange (i ≫ toSpec A ι) T₁.hom T₂.hom g.left (Over.w g) =
      (familyScheme (i ≫ toSpec A ι)).map g :=
  familyBaseChange_eq_familyScheme_map _ g

/-- **Openness** on a locally Noetherian `T`: `C_φ` is open and closed, `C_m` is open, and so is
the stratum condition of `Pic^φ_m`. -/
example [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] [IsLocallyNoetherian T] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (φ : ℚ[X]) (m : ℤ)
    (r : ℕ) :
    IsClopen {t : T | HasFiberDualEulerPolynomial i s φ L t} ∧
      IsOpen {t : T | HasFiberTwistVanishingAndSections i s m L t} ∧
      IsOpen {t : T | HasFiberTwistVanishing i s m L t ∧ ¬ HasFiberTwistSections i s m L t} ∧
      IsOpen {t : T | HasFiberTwistVanishing i s m L t ∧ fiberTwistDim i s L t m 0 = r} ∧
      IsOpen {t : T | IsFiberStratum i s φ m L t} :=
  ⟨isClopen_setOf_hasFiberDualEulerPolynomial i s N e L φ,
    isOpen_setOf_hasFiberTwistVanishingAndSections i s N e L m,
    isOpen_setOf_hasFiberTwistVanishing_and_not_hasFiberTwistSections i s N e L m,
    isOpen_setOf_hasFiberTwistVanishing_and_fiberTwistDim_zero_eq i s N e L m r,
    isOpen_setOf_isFiberStratum i s N e L φ m⟩

/-- **Monotonicity** in `m`, and the **cover**: a unique Hilbert polynomial at each point, and
the conditions `C_m` for `m ≫ 0` when the fibres are geometrically integral. -/
example [IsClosedImmersion i] [GeometricallyIntegral (i ≫ toSpec A ι)] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T)
    {m m' : ℤ} (h : m ≤ m') :
    (HasFiberTwistVanishingAndSections i s m L t →
        HasFiberTwistVanishingAndSections i s m' L t) ∧
      (∃ φ : ℚ[X], HasFiberDualEulerPolynomial i s φ L t) ∧
      (∀ φ φ' : ℚ[X], HasFiberDualEulerPolynomial i s φ L t →
        HasFiberDualEulerPolynomial i s φ' L t → φ = φ') ∧
      (∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → HasFiberTwistVanishingAndSections i s m L t) ∧
      (∃ φ : ℚ[X], ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → IsFiberStratum i s φ m L t) :=
  ⟨fun hc => hc.mono i s L t N e h, exists_hasFiberDualEulerPolynomial i s L t N e,
    fun _ _ hφ hφ' => hφ.unique i s L t hφ',
    exists_forall_hasFiberTwistVanishingAndSections i s L t N e,
    exists_isFiberStratum i s L t N e⟩

/-- **The twist** `L ↦ L(m)` carries `Pic^φ_m` onto `Pic^{φ₀}_0` with `φ₀(n) = φ(n - m)`, and
shifts the fibre invariants. -/
example [IsClosedImmersion i] (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T)
    (φ : ℚ[X]) (m n : ℤ) (q : ℕ) :
    fiberTwistDim i s (pulledTwistLineBundle i s m L) t n q = fiberTwistDim i s L t (n + m) q ∧
      fiberDualTwistEulerChar i s (pulledTwistLineBundle i s m L) t n =
        fiberDualTwistEulerChar i s L t (n - m) ∧
      (IsFiberStratum i s (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) 0
        (pulledTwistLineBundle i s m L) t ↔ IsFiberStratum i s φ m L t) :=
  ⟨fiberTwistDim_pulledTwistLineBundle i s L t m n q,
    fiberDualTwistEulerChar_pulledTwistLineBundle i s L t m n,
    isFiberStratum_pulledTwistLineBundle_iff i s L t φ m⟩

/-- **Twisting classes**: `[L(n)] = [L] + n • o_T(1)`, and the Picard presheaf map sends
`a + n • o_T(1)` to `g^* a + n • o_{T'}(1)`. -/
example (n : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s))
    {T₁ T₂ : Over (Spec (CommRingCat.of A))} (g : T₂ ⟶ T₁)
    (a : PicardGroup (pullback (i ≫ toSpec A ι) T₁.hom)) :
    classOf _ (pulledTwistLineBundle i s n L) = classOf _ L + n • fiberTwistClass i s 1 ∧
      ((familyPicardFunctor (i ≫ toSpec A ι)).map g.op).hom
          (a + n • fiberTwistClass i T₁.hom 1) =
        (show PicardGroup (pullback (i ≫ toSpec A ι) T₂.hom) from
          ((familyPicardFunctor (i ≫ toSpec A ι)).map g.op).hom a) +
          n • fiberTwistClass i T₂.hom 1 :=
  ⟨classOf_pulledTwistLineBundle i s n L,
    familyPicardFunctor_map_add_zsmul_fiberTwistClass i g a n⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isOpen_setOf_hasFiberTwistVanishingAndSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isOpen_setOf_hasFiberTwistVanishingAndSections

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isClopen_setOf_hasFiberDualEulerPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClopen_setOf_hasFiberDualEulerPolynomial

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.hasFiberDualEulerPolynomial_pullback_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hasFiberDualEulerPolynomial_pullback_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.hasFiberTwistVanishingAndSections_pullback_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hasFiberTwistVanishingAndSections_pullback_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.HasFiberTwistVanishingAndSections.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms HasFiberTwistVanishingAndSections.mono

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_isFiberStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_isFiberStratum

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isFiberStratum_pulledTwistLineBundle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isFiberStratum_pulledTwistLineBundle_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familyPicardFunctor_map_add_zsmul_fiberTwistClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyPicardFunctor_map_add_zsmul_fiberTwistClass
