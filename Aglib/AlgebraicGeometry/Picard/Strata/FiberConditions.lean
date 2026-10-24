/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Family
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Monotone
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Twist
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Picard.Presheaf
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The fibre conditions defining the strata of the Picard functor

Let `A` be a commutative ring, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed immersion with
`ι ≃ Fin (N + 1)`, and `f = i ≫ toSpec A ι`. For a scheme `s : T ⟶ Spec A`, a line bundle `L` on
`X_T = X ×_{Spec A} T` and a point `t ∈ T`, let `L_t` be the pullback of `L` to the fibre
`X_t = X ×_{Spec A} Spec κ(t)` and `L_t(n) = O(n) ⊗ L_t`, with `O(n)` pulled back from `P^N_A`.
The strata of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–30,
with the repairs of the Picard plan (Representability, step 2), are defined by two conditions:

* `C_φ = HasFiberDualEulerPolynomial i s φ L t`: `χ(X_t, L_t^{-1}(n)) = φ(n)` for every `n : ℤ`
  (Kleiman (4.8.1), p. 28; the stratum `Pic^φ`);
* `C_m = HasFiberTwistVanishingAndSections i s m L t`: `h^q(X_t, L_t(n)) = 0` for every `q ≥ 1`
  and `n ≥ m` (Kleiman (4.8.3), p. 29; `HasFiberTwistVanishing`, equivalently
  `H^q(X_t, L_t(n)) = 0` by `fiberTwistDim_eq_zero_iff`) and `h^0(X_t, L_t(m)) ≠ 0`
  (`HasFiberTwistSections`, the plan's nonvanishing condition: `O(-1)` on `P^1` satisfies the
  vanishing for `m = 0` and has no sections, and Kleiman's proof on p. 30 needs
  `H^0(X_t, L_t) ≠ 0`). The nonvanishing condition alone is closed, not open, so `C_m` is one
  condition, and `Pic^φ_m` is `C_φ ∧ C_m` (`IsFiberStratum`).

Here `h^q` is `fiberTwistDim`, the dimension over `κ(t)` of the original cohomology, and
`χ(X_t, L_t^{-1}(n))` is `fiberDualTwistEulerChar`, for the actual dual line bundle
`dualLineBundle`. The results are stated pointwise, in the shape of the fibre conditions of the
open-subsheaf lemma:

* **Isomorphism invariance** (`hasFiberDualEulerPolynomial_congr`,
  `hasFiberTwistVanishingAndSections_congr`, `isFiberStratum_congr`, and for the parts).
* **Base-change invariance**: for `b : T' ⟶ T` over `Spec A`, with the base-change map
  `familyBaseChange (i ≫ toSpec A ι) s s' b hb`, which is the map of `familyScheme`
  (`familyBaseChange_eq_familyScheme_map`), each condition holds for `b^* L` at `t'` if and only if
  it holds for `L` at `b t'` (`hasFiberDualEulerPolynomial_pullback_iff`,
  `hasFiberTwistVanishingAndSections_pullback_iff`, `isFiberStratum_pullback_iff`); the dimensions
  agree (`fiberTwistDim_familyBaseChange`, `fiberDualTwistEulerChar_familyBaseChange`). This is the
  fibre comparison `H^i(X_{t'}, L_{t'}(n)) = H^i(X_{p(t')}, L_{p(t')}(n)) ⊗ k_{t'}` of Kleiman,
  pp. 28–29 (flat base change over a field extension).
* **Openness** for locally Noetherian `T` and `f` flat: `C_φ` is open and closed
  (`isClopen_setOf_hasFiberDualEulerPolynomial`), `C_m` is open
  (`isOpen_setOf_hasFiberTwistVanishingAndSections`: on the vanishing locus `h^0 = χ` is locally
  constant), inside the vanishing locus the nonvanishing condition is open and closed
  (`isOpen_setOf_hasFiberTwistVanishing_and_not_hasFiberTwistSections`), and so is every level
  `h^0 = r` (`isOpen_setOf_hasFiberTwistVanishing_and_fiberTwistDim_zero_eq`). The stratum
  condition is open (`isOpen_setOf_isFiberStratum`).
* **Monotonicity in `m`** (`HasFiberTwistVanishingAndSections.mono`, `IsFiberStratum.mono`) and
  the **cover**: every point has a unique Hilbert polynomial (`exists_hasFiberDualEulerPolynomial`,
  `HasFiberDualEulerPolynomial.unique`), and if the fibres of `f` are geometrically integral, `C_m`
  holds for every `m ≫ 0` (`exists_forall_hasFiberTwistVanishingAndSections`,
  `exists_isFiberStratum`).
* **Twisting classes**: `o_T(n) = fiberTwistClass i s n`, the class of `O_{X_T}(n)`, is
  `n • o_T(1)` (`fiberTwistClass_eq_zsmul`), `[L(n)] = [L] + n • o_T(1)`
  (`classOf_pulledTwistLineBundle`), and the Picard presheaf sends `a + n • o_T(1)` to
  `g^* a + n • o_{T'}(1)` (`familyPicardFunctor_map_add_zsmul_fiberTwistClass`).
* **The twist** `L ↦ L(m)`: `h^q(X_t, (L(m))_t(n)) = h^q(X_t, L_t(n + m))` and
  `χ(X_t, (L(m))_t^{-1}(n)) = χ(X_t, L_t^{-1}(n - m))`, so `L(m)` satisfies `C_{φ₀} ∧ C_0` with
  `φ₀(n) = φ(n - m)` exactly when `L` satisfies `C_φ ∧ C_m`
  (`isFiberStratum_pulledTwistLineBundle_iff`). Kleiman's twist formula `φ₀(n) = φ(m + n)` on p. 29
  is a misprint for `φ₀(n) = φ(n - m)` (plan, Representability step 2).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard

section Classes

variable {Y Z : Scheme.{u}}

/-- The dual of a pulled-back line bundle is the pullback of the dual, up to isomorphism. -/
theorem nonempty_pullback_dualLineBundle_iso (u : Y ⟶ Z) (L : LineBundle Z) :
    Nonempty ((Scheme.Modules.pullback u).obj (dualLineBundle Z L).val ≅
      (dualLineBundle Y (pullbackLineBundle u L)).val) := by
  refine (class_eq_iff Y (pullbackLineBundle u (dualLineBundle Z L))
    (dualLineBundle Y (pullbackLineBundle u L))).mp ?_
  change classOf Y (pullbackLineBundle u (dualLineBundle Z L)) =
    classOf Y (dualLineBundle Y (pullbackLineBundle u L))
  rw [← pullbackClass_classOf, classOf_dual, PullbackTensor.Local.pullbackClass_neg,
    pullbackClass_classOf, classOf_dual]

/-- Duals of isomorphic line bundles are isomorphic. -/
theorem nonempty_dualLineBundle_iso {L L' : LineBundle Z} (e : L.val ≅ L'.val) :
    Nonempty ((dualLineBundle Z L).val ≅ (dualLineBundle Z L').val) := by
  refine (class_eq_iff Z (dualLineBundle Z L) (dualLineBundle Z L')).mp ?_
  change classOf Z (dualLineBundle Z L) = classOf Z (dualLineBundle Z L')
  rw [classOf_dual, classOf_dual, show classOf Z L = classOf Z L' from Quotient.sound ⟨e⟩]

end Classes

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) {T : Scheme.{u}} (s : T ⟶ Spec (.of A))

/-- `h^q(X_t, L_t(n))`: the dimension over `κ(t)` of the cohomology of `O(n) ⊗ L_t` on the fibre
`X_t = X ×_{Spec A} Spec κ(t)`. -/
abbrev fiberTwistDim (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (n : ℤ) (q : ℕ) :
    ℕ :=
  embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ s)
    ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj L.val) n q

/-- `χ(X_t, L_t^{-1}(n))`, for the actual dual line bundle `L^{-1} = dualLineBundle L`. -/
abbrev fiberDualTwistEulerChar (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (n : ℤ) :
    ℤ :=
  embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ s)
    ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj
      (dualLineBundle _ L).val) n

/-- Kleiman's condition (4.8.1) (arXiv:math/0504020v1, p. 28) at `t`:
`χ(X_t, L_t^{-1}(n)) = φ(n)` for every `n : ℤ`. -/
def HasFiberDualEulerPolynomial (φ : Polynomial ℚ) (L : LineBundle (pullback (i ≫ toSpec A ι) s))
    (t : T) : Prop :=
  ∀ n : ℤ, (fiberDualTwistEulerChar i s L t n : ℚ) = φ.eval (n : ℚ)

/-- Kleiman's condition (4.8.3) (arXiv:math/0504020v1, p. 29) at `t`:
`h^q(X_t, L_t(n)) = 0` for every `q ≥ 1` and `n ≥ m`. -/
def HasFiberTwistVanishing (m : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    Prop :=
  ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n → fiberTwistDim i s L t n q = 0

/-- The nonvanishing condition of the plan's `Pic^φ_m` at `t`: `h^0(X_t, L_t(m)) ≠ 0`. -/
def HasFiberTwistSections (m : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    Prop :=
  fiberTwistDim i s L t m 0 ≠ 0

/-- The condition `C_m` of the stratum `Pic^φ_m` at `t`, as one fibre condition:
`h^q(X_t, L_t(n)) = 0` for `q ≥ 1` and `n ≥ m`, and `h^0(X_t, L_t(m)) ≠ 0`. The nonvanishing
condition alone is closed, not open, in `t` (upper semicontinuity); the conjunction is open
(`isOpen_setOf_hasFiberTwistVanishingAndSections`). -/
def HasFiberTwistVanishingAndSections (m : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s))
    (t : T) : Prop :=
  HasFiberTwistVanishing i s m L t ∧ HasFiberTwistSections i s m L t

/-- The condition defining the stratum `Pic^φ_m` at `t` (Kleiman, arXiv:math/0504020v1, p. 29,
with the nonvanishing condition of the plan's repair): `C_φ ∧ C_m`. -/
def IsFiberStratum (φ : Polynomial ℚ) (m : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s))
    (t : T) : Prop :=
  HasFiberDualEulerPolynomial i s φ L t ∧ HasFiberTwistVanishingAndSections i s m L t

/-! ### Invariance under isomorphism -/

section Congr

variable {L L' : LineBundle (pullback (i ≫ toSpec A ι) s)} (e : L.val ≅ L'.val) (t : T)

include e in
theorem fiberTwistDim_congr (n : ℤ) (q : ℕ) :
    fiberTwistDim i s L t n q = fiberTwistDim i s L' t n q :=
  embeddedFiberTwistDim_congr i _ ((Scheme.Modules.pullback _).mapIso e) n q

include e in
theorem fiberDualTwistEulerChar_congr (n : ℤ) :
    fiberDualTwistEulerChar i s L t n = fiberDualTwistEulerChar i s L' t n := by
  obtain ⟨e'⟩ := nonempty_dualLineBundle_iso e
  exact embeddedFiberTwistEulerChar_congr i _ ((Scheme.Modules.pullback _).mapIso e') n

include e in
theorem hasFiberDualEulerPolynomial_congr (φ : Polynomial ℚ) :
    HasFiberDualEulerPolynomial i s φ L t ↔ HasFiberDualEulerPolynomial i s φ L' t := by
  simp only [HasFiberDualEulerPolynomial, fiberDualTwistEulerChar_congr i s e t]

include e in
theorem hasFiberTwistVanishing_congr (m : ℤ) :
    HasFiberTwistVanishing i s m L t ↔ HasFiberTwistVanishing i s m L' t := by
  simp only [HasFiberTwistVanishing, fiberTwistDim_congr i s e t]

include e in
theorem hasFiberTwistSections_congr (m : ℤ) :
    HasFiberTwistSections i s m L t ↔ HasFiberTwistSections i s m L' t := by
  simp only [HasFiberTwistSections, fiberTwistDim_congr i s e t]

include e in
theorem hasFiberTwistVanishingAndSections_congr (m : ℤ) :
    HasFiberTwistVanishingAndSections i s m L t ↔ HasFiberTwistVanishingAndSections i s m L' t :=
  and_congr (hasFiberTwistVanishing_congr i s e t m) (hasFiberTwistSections_congr i s e t m)

include e in
theorem isFiberStratum_congr (φ : Polynomial ℚ) (m : ℤ) :
    IsFiberStratum i s φ m L t ↔ IsFiberStratum i s φ m L' t :=
  and_congr (hasFiberDualEulerPolynomial_congr i s e t φ)
    (hasFiberTwistVanishingAndSections_congr i s e t m)

end Congr

/-! ### Invariance under base change of the family -/

section BaseChange

variable [IsProper (i ≫ toSpec A ι)] {T' : Scheme.{u}} (s' : T' ⟶ Spec (.of A)) (b : T' ⟶ T)
  (hb : b ≫ s = s') (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t' : T')

/-- **Fibre dimensions of a pulled-back family**: for `b : T' ⟶ T` over `Spec A`,
`h^q(X_{t'}, (b^* L)_{t'}(n)) = h^q(X_{b t'}, L_{b t'}(n))`. -/
theorem fiberTwistDim_familyBaseChange (n : ℤ) (q : ℕ) :
    fiberTwistDim i s' (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' n q =
      fiberTwistDim i s L (b t') n q :=
  embeddedFiberTwistDim_familyBaseChange i s s' b hb L t' n q

/-- **Fibre Euler characteristics of a pulled-back family**: for `b : T' ⟶ T` over `Spec A`,
`χ(X_{t'}, (b^* L)_{t'}^{-1}(n)) = χ(X_{b t'}, L_{b t'}^{-1}(n))`. -/
theorem fiberDualTwistEulerChar_familyBaseChange (n : ℤ) :
    fiberDualTwistEulerChar i s'
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' n =
      fiberDualTwistEulerChar i s L (b t') n := by
  obtain ⟨e⟩ := nonempty_pullback_dualLineBundle_iso (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L
  exact (embeddedFiberTwistEulerChar_congr i _ ((Scheme.Modules.pullback _).mapIso e.symm) n).trans
    (embeddedFiberTwistEulerChar_familyBaseChange i s s' b hb (dualLineBundle _ L) t' n)

theorem hasFiberDualEulerPolynomial_pullback_iff (φ : Polynomial ℚ) :
    HasFiberDualEulerPolynomial i s' φ
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
      HasFiberDualEulerPolynomial i s φ L (b t') := by
  simp only [HasFiberDualEulerPolynomial, fiberDualTwistEulerChar_familyBaseChange i s s' b hb L t']

theorem hasFiberTwistVanishing_pullback_iff (m : ℤ) :
    HasFiberTwistVanishing i s' m
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
      HasFiberTwistVanishing i s m L (b t') := by
  simp only [HasFiberTwistVanishing, fiberTwistDim_familyBaseChange i s s' b hb L t']

theorem hasFiberTwistSections_pullback_iff (m : ℤ) :
    HasFiberTwistSections i s' m
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
      HasFiberTwistSections i s m L (b t') := by
  simp only [HasFiberTwistSections, fiberTwistDim_familyBaseChange i s s' b hb L t']

theorem hasFiberTwistVanishingAndSections_pullback_iff (m : ℤ) :
    HasFiberTwistVanishingAndSections i s' m
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
      HasFiberTwistVanishingAndSections i s m L (b t') :=
  and_congr (hasFiberTwistVanishing_pullback_iff i s s' b hb L t' m)
    (hasFiberTwistSections_pullback_iff i s s' b hb L t' m)

theorem isFiberStratum_pullback_iff (φ : Polynomial ℚ) (m : ℤ) :
    IsFiberStratum i s' φ m
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
      IsFiberStratum i s φ m L (b t') :=
  and_congr (hasFiberDualEulerPolynomial_pullback_iff i s s' b hb L t' φ)
    (hasFiberTwistVanishingAndSections_pullback_iff i s s' b hb L t' m)

end BaseChange

/-! ### Vanishing of cohomology and its dimension -/

/-- On the fibre, `h^q(X_t, L_t(n)) = 0` exactly when `H^q(X_t, L_t(n))` vanishes, since the
cohomology is finite-dimensional (`moduleCohomology_finite_of_projectiveEmbedding`). -/
theorem fiberTwistDim_eq_zero_iff [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (n : ℤ) (q : ℕ) :
    fiberTwistDim i s L t n q = 0 ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _
        (pulledTwist (pullback.fst (i ≫ toSpec A ι) (T.fromSpecResidueField t ≫ s) ≫ i) n
          ((Scheme.Modules.pullback
            (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj L.val))) q) := by
  exact embeddedFiberTwistDim_eq_zero_iff i (K := T.residueField t) _ N e _ n
    (affineLocallyFiniteType_of_isLocallyRankOne
      (isLocallyRankOne_pulledTwist _ n (Invertible.pullback_locallyRankOne _ _ L.property))) q

/-! ### Openness in families -/

section Openness

variable [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] [IsLocallyNoetherian T] (N : ℕ)
  (e : ι ≃ Fin (N + 1)) (L : LineBundle (pullback (i ≫ toSpec A ι) s))

include e in
/-- **The locus of `C_φ` is open and closed** on a locally Noetherian `T`: the set of `t` with
`χ(X_t, L_t^{-1}(n)) = φ(n)` for every `n` (Kleiman, arXiv:math/0504020v1, p. 28: `T'^φ` is open
by EGA III₂ 7.9.11; p. 29: the `T'^φ` are disjoint and cover `T'`). -/
theorem isClopen_setOf_hasFiberDualEulerPolynomial (φ : Polynomial ℚ) :
    IsClopen {t : T | HasFiberDualEulerPolynomial i s φ L t} := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact isClopen_setOf_embeddedFiberTwistEulerChar_eq i s (dualLineBundle _ L)
    (fun n => φ.eval (n : ℚ))

include e in
/-- **The vanishing condition is open** (Kleiman, arXiv:math/0504020v1, p. 29): on a locally
Noetherian `T`, the set of `t` with `h^q(X_t, L_t(n)) = 0` for `q ≥ 1` and `n ≥ m`. -/
theorem isOpen_setOf_hasFiberTwistVanishing (m : ℤ) :
    IsOpen {t : T | HasFiberTwistVanishing i s m L t} := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero i s L N e m

include e in
/-- **The condition `C_m` is open**: on the vanishing locus `h^0(X_t, L_t(m)) = χ(X_t, L_t(m))`
is locally constant, so vanishing together with nonvanishing is an open condition on a locally
Noetherian `T`. -/
theorem isOpen_setOf_hasFiberTwistVanishingAndSections (m : ℤ) :
    IsOpen {t : T | HasFiberTwistVanishingAndSections i s m L t} := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_ne_zero i s L N e m

include e in
/-- Inside the vanishing locus the nonvanishing condition is open and closed: its failure is
open as well. -/
theorem isOpen_setOf_hasFiberTwistVanishing_and_not_hasFiberTwistSections (m : ℤ) :
    IsOpen {t : T | HasFiberTwistVanishing i s m L t ∧ ¬ HasFiberTwistSections i s m L t} := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have h := isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_eq_zero i s L N e m
  convert h using 3 with t
  simp only [HasFiberTwistSections, not_not]
  rfl

include e in
/-- **Refinement by the number of sections**: for every `r`, the set of `t` where the vanishing
condition holds and `h^0(X_t, L_t(m)) = r` is open (and closed in the vanishing locus). -/
theorem isOpen_setOf_hasFiberTwistVanishing_and_fiberTwistDim_zero_eq (m : ℤ) (r : ℕ) :
    IsOpen {t : T | HasFiberTwistVanishing i s m L t ∧ fiberTwistDim i s L t m 0 = r} := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_eq i s L N e m r

include e in
/-- **The stratum condition of `Pic^φ_m` is open** on a locally Noetherian `T`. -/
theorem isOpen_setOf_isFiberStratum (φ : Polynomial ℚ) (m : ℤ) :
    IsOpen {t : T | IsFiberStratum i s φ m L t} :=
  (isClopen_setOf_hasFiberDualEulerPolynomial i s N e L φ).isOpen.inter
    (isOpen_setOf_hasFiberTwistVanishingAndSections i s N e L m)

end Openness

/-! ### Monotonicity and cover -/

section Cover

variable (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T)

/-- The vanishing condition at `m` implies it at every `m' ≥ m`. -/
theorem HasFiberTwistVanishing.mono {m m' : ℤ} (h : m ≤ m')
    (hv : HasFiberTwistVanishing i s m L t) : HasFiberTwistVanishing i s m' L t :=
  fun q hq n hn => hv q hq n (h.trans hn)

/-- **Monotonicity of the nonvanishing condition** (the plan's `Pic^φ_m ⊆ Pic^φ_{m+1}`):
`h^0(X_t, L_t(m)) ≠ 0` implies `h^0(X_t, L_t(m')) ≠ 0` for `m' ≥ m`, by multiplication with a
general section of `O(1)` after extending `κ(t)` to an algebraic closure
(`embeddedFiberTwistDim_zero_mono`). -/
theorem HasFiberTwistSections.mono [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    {m m' : ℤ} (h : m ≤ m') (hs : HasFiberTwistSections i s m L t) :
    HasFiberTwistSections i s m' L t :=
  embeddedFiberTwistDim_zero_ne_zero_of_le i N e _
    (pullbackLineBundle (residueFieldBaseChange (i ≫ toSpec A ι) s t) L) h hs

/-- **The condition `C_m` is monotone in `m`.** -/
theorem HasFiberTwistVanishingAndSections.mono [IsClosedImmersion i] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) {m m' : ℤ} (h : m ≤ m')
    (hc : HasFiberTwistVanishingAndSections i s m L t) :
    HasFiberTwistVanishingAndSections i s m' L t :=
  ⟨hc.1.mono i s L t h, hc.2.mono i s L t N e h⟩

/-- **The strata `Pic^φ_m` increase with `m`.** -/
theorem IsFiberStratum.mono [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    {φ : Polynomial ℚ} {m m' : ℤ} (h : m ≤ m') (hst : IsFiberStratum i s φ m L t) :
    IsFiberStratum i s φ m' L t :=
  ⟨hst.1, hst.2.mono i s L t N e h⟩

/-- **Every point lies in some `Pic^φ`**: `n ↦ χ(X_t, L_t^{-1}(n))` is a polynomial
(Stacks, Tag 08AC). -/
theorem exists_hasFiberDualEulerPolynomial [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1)) :
    ∃ φ : Polynomial ℚ, HasFiberDualEulerPolynomial i s φ L t :=
  exists_embeddedFiberTwistEulerChar_eq_eval i _ N e _
    (affineLocallyFiniteType_of_isLocallyRankOne
      (Invertible.pullback_locallyRankOne _ _ (dualLineBundle _ L).property))

/-- **The strata `Pic^φ` are disjoint**: the polynomial is unique. -/
theorem HasFiberDualEulerPolynomial.unique {φ φ' : Polynomial ℚ}
    (h : HasFiberDualEulerPolynomial i s φ L t) (h' : HasFiberDualEulerPolynomial i s φ' L t) :
    φ = φ' := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n : ℚ)) Int.cast_injective
  intro n
  change φ.eval (n : ℚ) = φ'.eval (n : ℚ)
  rw [← h n, ← h' n]

/-- **The strata `Pic^φ_m` cover `Pic^φ`**: if the fibres of `f` are geometrically integral, then
for every `t` the vanishing and nonvanishing conditions hold for all `m ≫ 0` (Serre vanishing on
`X_t`, and global generation of large twists, Nitsure, arXiv:math/0504590v1, Lemma 2.1 (c),
p. 10). -/
theorem exists_forall_hasFiberTwistVanishingAndSections [IsClosedImmersion i]
    [GeometricallyIntegral (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1)) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → HasFiberTwistVanishingAndSections i s m L t := by
  let k : Spec (.of (T.residueField t)) ⟶ Spec (.of A) := T.fromSpecResidueField t ≫ s
  have : IsIntegral (pullback (i ≫ toSpec A ι) k) :=
    pullback_of_geometrically GeometricallyIntegral.geometrically_isIntegral _ k
  have hM : affineLocallyFiniteType _
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj L.val) :=
    affineLocallyFiniteType_of_isLocallyRankOne
      (Invertible.pullback_locallyRankOne _ _ L.property)
  have hM0 : ¬ IsZero
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj L.val) :=
    fun hz => lineBundle_id_ne_zero _
      (pullbackLineBundle (residueFieldBaseChange (i ≫ toSpec A ι) s t) L)
      ((IsZero.iff_id_eq_zero _).mp hz)
  obtain ⟨B₁, hB₁⟩ := exists_embeddedFiberTwistDim_eq_zero i k N e _ hM
  obtain ⟨B₂, hB₂⟩ := exists_embeddedFiberTwistDim_zero_ne_zero i k N e _ hM hM0
  refine ⟨max B₁ B₂, fun m hm => ⟨fun q hq n hn => hB₁ n ?_ q hq, hB₂ m ?_⟩⟩
  · exact (le_max_left _ _).trans (hm.trans hn)
  · exact (le_max_right _ _).trans hm

/-- **The strata `Pic^φ_m` cover**: with geometrically integral fibres, every point lies in
`Pic^φ_m` for its Hilbert polynomial `φ` and all `m ≫ 0`. -/
theorem exists_isFiberStratum [IsClosedImmersion i] [GeometricallyIntegral (i ≫ toSpec A ι)]
    (N : ℕ) (e : ι ≃ Fin (N + 1)) :
    ∃ φ : Polynomial ℚ, ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → IsFiberStratum i s φ m L t := by
  obtain ⟨φ, hφ⟩ := exists_hasFiberDualEulerPolynomial i s L t N e
  obtain ⟨m₀, hm₀⟩ := exists_forall_hasFiberTwistVanishingAndSections i s L t N e
  exact ⟨φ, m₀, fun m hm => ⟨hφ, hm₀ m hm⟩⟩

end Cover

/-! ### The base-change map and twisting classes -/

section Twist

/-- The base-change map `X ×_S T' ⟶ X ×_S T` of the statements above is the map of the family
`familyScheme p` of the Picard functor. -/
theorem familyBaseChange_eq_familyScheme_map {S X' : Scheme.{u}} (p : X' ⟶ S) {T T' : Over S}
    (g : T' ⟶ T) : familyBaseChange p T.hom T'.hom g.left (Over.w g) = (familyScheme p).map g :=
  rfl

/-- The class of `O(n)` on `P^N_A` is `n` times the class of `O(1)`. -/
theorem classOf_twistingLineBundle_eq_zsmul (n : ℤ) :
    classOf _ (twistingLineBundle A ι n) = n • classOf _ (twistingLineBundle A ι 1) := by
  have hadd (a b : ℤ) : classOf _ (twistingLineBundle A ι (a + b)) =
      classOf _ (twistingLineBundle A ι a) + classOf _ (twistingLineBundle A ι b) :=
    Quotient.sound ⟨(twistingTensorIso A ι a b).symm⟩
  have hzero : classOf _ (twistingLineBundle A ι 0) = 0 :=
    Quotient.sound ⟨twistingZeroIso A ι ≪≫ (coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit (ProjectiveSpace A ι).ringCatSheaf)).symm⟩
  induction n using Int.induction_on with
  | zero => rw [hzero, zero_smul]
  | succ n ih => rw [hadd, ih, add_smul, one_smul]
  | pred n ih =>
    have h := hadd (-(n : ℤ) - 1) 1
    rw [sub_add_cancel, ih] at h
    rw [sub_smul, one_smul, h, add_sub_cancel_right]

/-- `o_T(n)`: the class of `O_{X_T}(n)`, the pullback of `O(n)` along `X_T ⟶ X ⟶ P^N_A`, in
`Pic(X_T)`. -/
def fiberTwistClass (n : ℤ) : PicardGroup (pullback (i ≫ toSpec A ι) s) :=
  pullbackClass (pullback.fst (i ≫ toSpec A ι) s ≫ i) (classOf _ (twistingLineBundle A ι n))

theorem fiberTwistClass_eq_zsmul (n : ℤ) : fiberTwistClass i s n = n • fiberTwistClass i s 1 := by
  unfold fiberTwistClass
  rw [classOf_twistingLineBundle_eq_zsmul, ← PullbackTensor.Local.pullbackHom_apply, map_zsmul,
    PullbackTensor.Local.pullbackHom_apply]

/-- The twisted line bundle `L(n) = O_{X_T}(n) ⊗ L`. -/
def pulledTwistLineBundle (n : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) :
    LineBundle (pullback (i ≫ toSpec A ι) s) :=
  ⟨pulledTwist (pullback.fst (i ≫ toSpec A ι) s ≫ i) n L.val,
    isLocallyRankOne_pulledTwist _ n L.property⟩

/-- The bundle `L(n)` has class `[L] + n • o_T(1)`. -/
theorem classOf_pulledTwistLineBundle (n : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) :
    classOf _ (pulledTwistLineBundle i s n L) = classOf _ L + n • fiberTwistClass i s 1 := by
  rw [← fiberTwistClass_eq_zsmul, add_comm]
  exact classOf_tensor _ (pullbackLineBundle (pullback.fst (i ≫ toSpec A ι) s ≫ i)
    (twistingLineBundle A ι n)) L

/-- **Naturality of the twisting classes**: `o_T(n)` pulls back to `o_{T'}(n)` along the
base-change map of `b : T' ⟶ T` over `Spec A`. -/
theorem pullbackClass_familyBaseChange_fiberTwistClass {T' : Scheme.{u}}
    (s' : T' ⟶ Spec (.of A)) (b : T' ⟶ T) (hb : b ≫ s = s') (n : ℤ) :
    pullbackClass (familyBaseChange (i ≫ toSpec A ι) s s' b hb) (fiberTwistClass i s n) =
      fiberTwistClass i s' n := by
  unfold fiberTwistClass
  rw [← pullbackClass_comp]
  congr 1
  simp [familyBaseChange]

/-- **Twisting naturality on the Picard presheaf**: the map of `familyPicardFunctor` along
`g : T' ⟶ T` sends `a + n • o_T(1)` to `g^* a + n • o_{T'}(1)`. -/
theorem familyPicardFunctor_map_add_zsmul_fiberTwistClass {T T' : Over (Spec (.of A))}
    (g : T' ⟶ T) (a : PicardGroup (pullback (i ≫ toSpec A ι) T.hom)) (n : ℤ) :
    ((familyPicardFunctor (i ≫ toSpec A ι)).map g.op).hom (a + n • fiberTwistClass i T.hom 1) =
      (show PicardGroup (pullback (i ≫ toSpec A ι) T'.hom) from
        ((familyPicardFunctor (i ≫ toSpec A ι)).map g.op).hom a) +
        n • fiberTwistClass i T'.hom 1 := by
  rw [map_add, map_zsmul, familyPicardFunctor_map_apply _ g.op (fiberTwistClass i T.hom 1)]
  congr 2
  exact pullbackClass_familyBaseChange_fiberTwistClass i T.hom T'.hom g.left (Over.w g) 1

/-! ### Twisting by `O(m)` -/

variable [IsClosedImmersion i] (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T)

/-- **Twisting the bundle shifts the twist**: `h^q(X_t, (L(m))_t(n)) = h^q(X_t, L_t(n + m))`. -/
theorem fiberTwistDim_pulledTwistLineBundle (m n : ℤ) (q : ℕ) :
    fiberTwistDim i s (pulledTwistLineBundle i s m L) t n q = fiberTwistDim i s L t (n + m) q :=
  (embeddedFiberTwistDim_congr i _ (pulledTwistPullbackIso _ _ _
      (residueFieldBaseChange_fst_assoc (i ≫ toSpec A ι) s t i) m L.val) n q).trans
    (embeddedFiberTwistDim_pulledTwist i _ _ (affineLocallyFiniteType_of_isLocallyRankOne
      (Invertible.pullback_locallyRankOne _ _ L.property)) m n q)

omit [IsClosedImmersion i] in
/-- The dual of `L(m)` is `L^{-1}(-m)`, up to isomorphism. -/
theorem nonempty_dualLineBundle_pulledTwistLineBundle_iso (m : ℤ) :
    Nonempty ((dualLineBundle _ (pulledTwistLineBundle i s m L)).val ≅
      (pulledTwistLineBundle i s (-m) (dualLineBundle _ L)).val) := by
  refine (class_eq_iff _ (dualLineBundle _ (pulledTwistLineBundle i s m L))
    (pulledTwistLineBundle i s (-m) (dualLineBundle _ L))).mp ?_
  change classOf _ (dualLineBundle _ (pulledTwistLineBundle i s m L)) =
    classOf _ (pulledTwistLineBundle i s (-m) (dualLineBundle _ L))
  rw [classOf_dual, classOf_pulledTwistLineBundle, classOf_pulledTwistLineBundle, classOf_dual,
    neg_add, neg_smul]

/-- **Twisting the bundle shifts the dual twist**:
`χ(X_t, (L(m))_t^{-1}(n)) = χ(X_t, L_t^{-1}(n - m))`. -/
theorem fiberDualTwistEulerChar_pulledTwistLineBundle (m n : ℤ) :
    fiberDualTwistEulerChar i s (pulledTwistLineBundle i s m L) t n =
      fiberDualTwistEulerChar i s L t (n - m) := by
  obtain ⟨e⟩ := nonempty_dualLineBundle_pulledTwistLineBundle_iso i s L m
  refine (embeddedFiberTwistEulerChar_congr i _ ((Scheme.Modules.pullback _).mapIso e ≪≫
    pulledTwistPullbackIso _ _ _ (residueFieldBaseChange_fst_assoc (i ≫ toSpec A ι) s t i) (-m)
      (dualLineBundle _ L).val) n).trans ?_
  rw [embeddedFiberTwistEulerChar_pulledTwist i _ _ (affineLocallyFiniteType_of_isLocallyRankOne
    (Invertible.pullback_locallyRankOne _ _ (dualLineBundle _ L).property)) (-m) n,
    ← sub_eq_add_neg]

/-- **The twist `L ↦ L(m)` carries `Pic^φ` to `Pic^{φ₀}`** with `φ₀(n) = φ(n - m)` (the plan's
correction of Kleiman's `φ(m + n)`, arXiv:math/0504020v1, p. 29). -/
theorem hasFiberDualEulerPolynomial_pulledTwistLineBundle_iff (φ : Polynomial ℚ) (m : ℤ) :
    HasFiberDualEulerPolynomial i s (φ.comp (Polynomial.X - Polynomial.C (m : ℚ)))
        (pulledTwistLineBundle i s m L) t ↔ HasFiberDualEulerPolynomial i s φ L t := by
  simp only [HasFiberDualEulerPolynomial, fiberDualTwistEulerChar_pulledTwistLineBundle,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  constructor
  · intro h n
    have h' := h (n + m)
    rw [add_sub_cancel_right] at h'
    rw [h']
    push_cast
    ring_nf
  · intro h n
    rw [h (n - m)]
    push_cast
    rfl

/-- The twist `L ↦ L(m)` shifts the vanishing condition: (4.8.3) at `m'` for `L(m)` is (4.8.3) at
`m' + m` for `L`. -/
theorem hasFiberTwistVanishing_pulledTwistLineBundle_iff (m' m : ℤ) :
    HasFiberTwistVanishing i s m' (pulledTwistLineBundle i s m L) t ↔
      HasFiberTwistVanishing i s (m' + m) L t := by
  simp only [HasFiberTwistVanishing, fiberTwistDim_pulledTwistLineBundle]
  constructor
  · intro h q hq n hn
    have h' := h q hq (n - m) (by omega)
    rwa [sub_add_cancel] at h'
  · intro h q hq n hn
    exact h q hq (n + m) (by omega)

/-- The twist `L ↦ L(m)` shifts the nonvanishing condition. -/
theorem hasFiberTwistSections_pulledTwistLineBundle_iff (m' m : ℤ) :
    HasFiberTwistSections i s m' (pulledTwistLineBundle i s m L) t ↔
      HasFiberTwistSections i s (m' + m) L t := by
  simp only [HasFiberTwistSections, fiberTwistDim_pulledTwistLineBundle]

/-- The twist `L ↦ L(m)` shifts the condition `C_m`. -/
theorem hasFiberTwistVanishingAndSections_pulledTwistLineBundle_iff (m' m : ℤ) :
    HasFiberTwistVanishingAndSections i s m' (pulledTwistLineBundle i s m L) t ↔
      HasFiberTwistVanishingAndSections i s (m' + m) L t :=
  and_congr (hasFiberTwistVanishing_pulledTwistLineBundle_iff i s L t m' m)
    (hasFiberTwistSections_pulledTwistLineBundle_iff i s L t m' m)

/-- **The twist `L ↦ L(m)` carries `Pic^φ_m` onto `Pic^{φ₀}_0`**, `φ₀(n) = φ(n - m)`, pointwise
(Kleiman, arXiv:math/0504020v1, pp. 29–30, with the plan's correction of the twist formula). -/
theorem isFiberStratum_pulledTwistLineBundle_iff (φ : Polynomial ℚ) (m : ℤ) :
    IsFiberStratum i s (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) 0
        (pulledTwistLineBundle i s m L) t ↔ IsFiberStratum i s φ m L t := by
  rw [IsFiberStratum, IsFiberStratum, hasFiberDualEulerPolynomial_pulledTwistLineBundle_iff,
    hasFiberTwistVanishingAndSections_pulledTwistLineBundle_iff, zero_add]

end Twist

end AlgebraicGeometry.Scheme.RelativePicard
