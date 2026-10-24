/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.FiberConditions
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.ZeroTwist

/-!
# The structure polynomial and the rank of sections on the fibres of the Picard strata

This leaf adds the two pointwise conditions of the refined strata index `(φ, ψ, m, r)` of the
Picard plan (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8,
pp. 28–30), in the setting of `Picard/Strata/FiberConditions`: `i : X ⟶ P^N_A` (a closed
immersion with `ι ≃ Fin (N + 1)` where a statement needs it; the definitions need no hypothesis),
`f = i ≫ toSpec A ι`, `s : T ⟶ Spec A`, a line bundle `L` on `X_T` and `t ∈ T`.

* **The base condition `C_ψ`** (`HasFiberStructureEulerPolynomial i s ψ t`):
  `χ(X_t, O_{X_t}(n)) = ψ(n)` for every `n`, with `O_{X_t}` the restriction of the trivial line
  bundle of `X_T` (`fiberStructureEulerChar`, equal to `χ` of the structure module:
  `fiberStructureEulerChar_eq`). Kleiman makes `ψ` constant by shrinking `S` (p. 30); here it is a
  fibre condition. For `f` proper it is invariant under base change of the family
  (`hasFiberStructureEulerPolynomial_pullback_iff`) and depends only on the image of `t` in
  `Spec A` (`hasFiberStructureEulerPolynomial_iff_base`); for a closed immersion every point has
  a unique `ψ` (`exists_hasFiberStructureEulerPolynomial`,
  `HasFiberStructureEulerPolynomial.unique`), and for `f` also flat the locus is open and closed
  on locally Noetherian `T` (`isClopen_setOf_hasFiberStructureEulerPolynomial`). No Noetherian
  hypothesis on `A` is needed for these; over a Noetherian `A` only finitely many `ψ` occur
  (`finite_setOf_exists_hasFiberStructureEulerPolynomial`).
* **The level condition `C_{m,r}`** (`HasFiberTwistVanishingAndRank i s m r L t`):
  `h^q(X_t, L_t(n)) = 0` for `q ≥ 1`, `n ≥ m`, and `h^0(X_t, L_t(m)) = r`. It is invariant under
  isomorphism and base change (`hasFiberTwistVanishingAndRank_congr`,
  `hasFiberTwistVanishingAndRank_pullback_iff`), shifts under the twist `L ↦ L(m)`
  (`hasFiberTwistVanishingAndRank_pulledTwistLineBundle_iff`), is open on locally Noetherian `T`
  (`isOpen_setOf_hasFiberTwistVanishingAndRank`: on the vanishing locus `h^0 = χ` is locally
  constant), implies `C_m` for `r ≠ 0`, and with geometrically integral fibres it holds for some
  `r ≥ 1` at every `m ≫ 0` (`exists_forall_exists_hasFiberTwistVanishingAndRank`).
* **The bridge to cohomology and base change**: `C_{0,r}` at `t` gives the point-fibre dimension
  `r` of `L` in degree `0`
  (`HasFiberTwistVanishingAndRank.modulePointFiberCohomologyDimension_zero`) and the vanishing
  of its point-fibre cohomology in positive degrees
  (`HasFiberTwistVanishingAndRank.subsingleton_modulePointFiberCohomology`), the hypotheses of
  cohomology and base change for `p_* L` (statement 15a; Kleiman p. 30: "`H^1(X_t, L_t) = 0` for
  all `t ∈ T′`"), through the zero twist (`pulledTwistZeroIso`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) {T : Scheme.{u}} (s : T ⟶ Spec (.of A))

/-! ### The base condition `C_ψ` -/

/-- `χ(X_t, O_{X_t}(n))`, with `O_{X_t}` the restriction of the trivial line bundle of `X_T`. -/
abbrev fiberStructureEulerChar (t : T) (n : ℤ) : ℤ :=
  embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ s)
    ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s t)).obj
      (trivialLineBundle (pullback (i ≫ toSpec A ι) s)).val) n

/-- The fibre structure Euler characteristic is `χ(X_t, O(n) ⊗ O_{X_t})` for the structure
module `O_{X_t}`. -/
theorem fiberStructureEulerChar_eq (t : T) (n : ℤ) :
    fiberStructureEulerChar i s t n =
      embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ s)
        (SheafOfModules.unit _) n :=
  embeddedFiberTwistEulerChar_congr i _ (pullbackFreeIso _ PUnit.{u + 1} ≪≫ coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit _)) n

/-- **The base condition `C_ψ`** at `t`: `χ(X_t, O_{X_t}(n)) = ψ(n)` for every `n : ℤ` (the base
polynomial of the refined strata of the Picard plan; Kleiman, arXiv:math/0504020v1, p. 30). -/
def HasFiberStructureEulerPolynomial (ψ : Polynomial ℚ) (t : T) : Prop :=
  ∀ n : ℤ, (fiberStructureEulerChar i s t n : ℚ) = ψ.eval (n : ℚ)

section BaseChange

variable [IsProper (i ≫ toSpec A ι)] {T' : Scheme.{u}} (s' : T' ⟶ Spec (.of A)) (b : T' ⟶ T)
  (hb : b ≫ s = s') (t' : T')

include hb in
/-- The fibre structure Euler characteristics of a family are invariant under base change. -/
theorem fiberStructureEulerChar_familyBaseChange (n : ℤ) :
    fiberStructureEulerChar i s' t' n = fiberStructureEulerChar i s (b t') n :=
  (embeddedFiberTwistEulerChar_congr i _ ((Scheme.Modules.pullback _).mapIso
      (pullbackFreeIso (familyBaseChange (i ≫ toSpec A ι) s s' b hb) PUnit.{u + 1}).symm) n).trans
    (embeddedFiberTwistEulerChar_familyBaseChange i s s' b hb
      (trivialLineBundle (pullback (i ≫ toSpec A ι) s)) t' n)

include hb in
/-- **Base-change invariance of `C_ψ`**: for `b : T' ⟶ T` over `Spec A`, the base condition holds
at `t'` exactly when it holds at `b t'`. -/
theorem hasFiberStructureEulerPolynomial_pullback_iff (ψ : Polynomial ℚ) :
    HasFiberStructureEulerPolynomial i s' ψ t' ↔
      HasFiberStructureEulerPolynomial i s ψ (b t') := by
  simp only [HasFiberStructureEulerPolynomial,
    fiberStructureEulerChar_familyBaseChange i s s' b hb t']

end BaseChange

/-- `C_ψ` depends only on the image of the point in `Spec A`. -/
theorem hasFiberStructureEulerPolynomial_iff_base [IsProper (i ≫ toSpec A ι)] (ψ : Polynomial ℚ)
    (t : T) :
    HasFiberStructureEulerPolynomial i s ψ t ↔ HasFiberStructureEulerPolynomial i (𝟙 _) ψ (s t) :=
  hasFiberStructureEulerPolynomial_pullback_iff i (𝟙 _) s s (Category.comp_id s) t ψ

/-- **`C_ψ` is open and closed** on a locally Noetherian `T`, for `f` flat. -/
theorem isClopen_setOf_hasFiberStructureEulerPolynomial [IsClosedImmersion i]
    [Flat (i ≫ toSpec A ι)] [IsLocallyNoetherian T] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (ψ : Polynomial ℚ) :
    IsClopen {t : T | HasFiberStructureEulerPolynomial i s ψ t} := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact isClopen_setOf_embeddedFiberTwistEulerChar_eq i s
    (trivialLineBundle (pullback (i ≫ toSpec A ι) s)) (fun n => ψ.eval (n : ℚ))

/-- **Every point has a base polynomial** (Stacks, Tag 08AC). -/
theorem exists_hasFiberStructureEulerPolynomial [IsClosedImmersion i] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (t : T) : ∃ ψ : Polynomial ℚ, HasFiberStructureEulerPolynomial i s ψ t :=
  exists_embeddedFiberTwistEulerChar_eq_eval i _ N e _
    (affineLocallyFiniteType_of_isLocallyRankOne (Invertible.pullback_locallyRankOne _ _
      (trivialLineBundle (pullback (i ≫ toSpec A ι) s)).property))

/-- **The base polynomial is unique.** -/
theorem HasFiberStructureEulerPolynomial.unique {ψ ψ' : Polynomial ℚ} {t : T}
    (h : HasFiberStructureEulerPolynomial i s ψ t)
    (h' : HasFiberStructureEulerPolynomial i s ψ' t) : ψ = ψ' := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n : ℚ)) Int.cast_injective
  intro n
  change ψ.eval (n : ℚ) = ψ'.eval (n : ℚ)
  rw [← h n, ← h' n]

/-- **Over a Noetherian `A`, only finitely many base polynomials occur**: the loci of the `ψ` are
pairwise disjoint open sets covering the quasi-compact `Spec A`. -/
theorem finite_setOf_exists_hasFiberStructureEulerPolynomial [IsNoetherianRing A]
    [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1)) :
    {ψ : Polynomial ℚ | ∃ s : Spec (.of A),
      HasFiberStructureEulerPolynomial i (𝟙 (Spec (.of A))) ψ s}.Finite := by
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun ψ : Polynomial ℚ => {s : Spec (.of A) |
      HasFiberStructureEulerPolynomial i (𝟙 (Spec (.of A))) ψ s})
    (fun ψ => (isClopen_setOf_hasFiberStructureEulerPolynomial i (𝟙 _) N e ψ).isOpen)
    (fun s _ => Set.mem_iUnion.mpr (exists_hasFiberStructureEulerPolynomial i (𝟙 _) N e s))
  refine F.finite_toSet.subset ?_
  rintro ψ ⟨s, hs⟩
  obtain ⟨ψ', hψ', hs'⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ s))
  rwa [HasFiberStructureEulerPolynomial.unique i (𝟙 _) hs hs']

/-! ### The level condition `C_{m,r}` -/

/-- **The level condition `C_{m,r}`** at `t`: `h^q(X_t, L_t(n)) = 0` for `q ≥ 1` and `n ≥ m`, and
`h^0(X_t, L_t(m)) = r` (Picard plan; Kleiman (4.8.3), arXiv:math/0504020v1, p. 29). -/
def HasFiberTwistVanishingAndRank (m : ℤ) (r : ℕ) (L : LineBundle (pullback (i ≫ toSpec A ι) s))
    (t : T) : Prop :=
  HasFiberTwistVanishing i s m L t ∧ fiberTwistDim i s L t m 0 = r

/-- `C_{m,r}` is invariant under isomorphism. -/
theorem hasFiberTwistVanishingAndRank_congr {L L' : LineBundle (pullback (i ≫ toSpec A ι) s)}
    (e : L.val ≅ L'.val) (t : T) (m : ℤ) (r : ℕ) :
    HasFiberTwistVanishingAndRank i s m r L t ↔ HasFiberTwistVanishingAndRank i s m r L' t :=
  and_congr (hasFiberTwistVanishing_congr i s e t m) (by rw [fiberTwistDim_congr i s e t])

/-- **Base-change invariance of `C_{m,r}`**: for `b : T' ⟶ T` over `Spec A`, the condition holds for
`b^* L` at `t'` exactly when it holds for `L` at `b t'`. -/
theorem hasFiberTwistVanishingAndRank_pullback_iff [IsProper (i ≫ toSpec A ι)] {T' : Scheme.{u}}
    (s' : T' ⟶ Spec (.of A)) (b : T' ⟶ T) (hb : b ≫ s = s')
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t' : T') (m : ℤ) (r : ℕ) :
    HasFiberTwistVanishingAndRank i s' m r
        (pullbackLineBundle (familyBaseChange (i ≫ toSpec A ι) s s' b hb) L) t' ↔
      HasFiberTwistVanishingAndRank i s m r L (b t') :=
  and_congr (hasFiberTwistVanishing_pullback_iff i s s' b hb L t' m)
    (by rw [fiberTwistDim_familyBaseChange i s s' b hb L t'])

/-- **The twist shifts `C_{m,r}`**: `C_{m',r}` for `L(m)` is `C_{m'+m,r}` for `L`. -/
theorem hasFiberTwistVanishingAndRank_pulledTwistLineBundle_iff [IsClosedImmersion i]
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (m' m : ℤ) (r : ℕ) :
    HasFiberTwistVanishingAndRank i s m' r (pulledTwistLineBundle i s m L) t ↔
      HasFiberTwistVanishingAndRank i s (m' + m) r L t :=
  and_congr (hasFiberTwistVanishing_pulledTwistLineBundle_iff i s L t m' m)
    (by rw [fiberTwistDim_pulledTwistLineBundle])

/-- **`C_{m,r}` is open** on a locally Noetherian `T` for `f` flat. -/
theorem isOpen_setOf_hasFiberTwistVanishingAndRank [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
    [IsLocallyNoetherian T] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (m : ℤ) (r : ℕ) :
    IsOpen {t : T | HasFiberTwistVanishingAndRank i s m r L t} :=
  isOpen_setOf_hasFiberTwistVanishing_and_fiberTwistDim_zero_eq i s N e L m r

/-- The rank is unique. -/
theorem HasFiberTwistVanishingAndRank.rank_eq {L : LineBundle (pullback (i ≫ toSpec A ι) s)}
    {t : T} {m : ℤ} {r r' : ℕ} (h : HasFiberTwistVanishingAndRank i s m r L t)
    (h' : HasFiberTwistVanishingAndRank i s m r' L t) : r = r' :=
  h.2.symm.trans h'.2

/-- For `r ≠ 0`, `C_{m,r}` implies `C_m`. -/
theorem HasFiberTwistVanishingAndRank.hasFiberTwistVanishingAndSections
    {L : LineBundle (pullback (i ≫ toSpec A ι) s)} {t : T} {m : ℤ} {r : ℕ}
    (h : HasFiberTwistVanishingAndRank i s m r L t) (hr : r ≠ 0) :
    HasFiberTwistVanishingAndSections i s m L t :=
  ⟨h.1, fun h0 => hr (h.2.symm.trans h0)⟩

/-- `C_m` is the union of the `C_{m,r}` with `r ≥ 1`. -/
theorem hasFiberTwistVanishingAndSections_iff_exists
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (m : ℤ) :
    HasFiberTwistVanishingAndSections i s m L t ↔
      ∃ k : ℕ, HasFiberTwistVanishingAndRank i s m (k + 1) L t := by
  constructor
  · intro h
    refine ⟨fiberTwistDim i s L t m 0 - 1, h.1, ?_⟩
    exact (Nat.succ_pred_eq_of_ne_zero h.2).symm
  · rintro ⟨k, hk⟩
    exact hk.hasFiberTwistVanishingAndSections i s (Nat.succ_ne_zero k)

/-- **The level conditions cover**: with geometrically integral fibres, for every `m ≫ 0` some
`C_{m,r}` with `r ≥ 1` holds at `t`. -/
theorem exists_forall_exists_hasFiberTwistVanishingAndRank [IsClosedImmersion i]
    [GeometricallyIntegral (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∃ k : ℕ, HasFiberTwistVanishingAndRank i s m (k + 1) L t := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_hasFiberTwistVanishingAndSections i s L t N e
  exact ⟨m₀, fun m hm => (hasFiberTwistVanishingAndSections_iff_exists i s L t m).mp (hm₀ m hm)⟩

/-! ### The bridge to cohomology and base change -/

/-- **The bridge to cohomology and base change, degree `0`**: `C_{0,r}` at `t` gives the
point-fibre dimension `r` of `L` in degree `0`, a fibre hypothesis of cohomology and base change
for the direct image of `L` (Picard plan, statement 15a; Kleiman, arXiv:math/0504020v1, p. 30). -/
theorem HasFiberTwistVanishingAndRank.modulePointFiberCohomologyDimension_zero
    {L : LineBundle (pullback (i ≫ toSpec A ι) s)} {t : T} {r : ℕ}
    (h : HasFiberTwistVanishingAndRank i s 0 r L t) :
    modulePointFiberCohomologyDimension (pullback.snd (i ≫ toSpec A ι) s) L.val 0 t = r :=
  (modulePointFiberCohomologyDimension_eq_embeddedFiberTwistDim_zero i s L.val 0 t).trans h.2

/-- **The bridge to cohomology and base change, positive degrees**: `C_{0,r}` at `t` gives the
vanishing of the point-fibre cohomology of `L` in every positive degree, a fibre hypothesis of
cohomology and base change for the direct image of `L` (Picard plan, statement 15a; Kleiman,
arXiv:math/0504020v1, p. 30: "`H^1(X_t, L_t) = 0` for all `t ∈ T′`"). -/
theorem HasFiberTwistVanishingAndRank.subsingleton_modulePointFiberCohomology [IsClosedImmersion i]
    (N : ℕ) (e : ι ≃ Fin (N + 1)) {L : LineBundle (pullback (i ≫ toSpec A ι) s)} {t : T} {r : ℕ}
    (h : HasFiberTwistVanishingAndRank i s 0 r L t) {q : ℕ} (hq : 0 < q) :
    Subsingleton (modulePointFiberCohomology (pullback.snd (i ≫ toSpec A ι) s) L.val q t) :=
  (subsingleton_modulePointFiberCohomology_iff_embeddedFiberTwistDim_zero i s N e L q t).mpr
    (h.1 q hq 0 le_rfl)

end AlgebraicGeometry.Scheme.RelativePicard
