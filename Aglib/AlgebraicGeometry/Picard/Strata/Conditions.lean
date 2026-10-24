/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.BaseAndRank
public import Aglib.AlgebraicGeometry.Picard.FiberCondition.RelativeCover
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.ResidueFieldConcentration
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward

/-!
# The strata of the Picard functor as fibre conditions

Let `i : X ⟶ P^N_A = ProjectiveSpace A ι` be a closed immersion with `ι ≃ Fin (N + 1)`, such that
`p = i ≫ toSpec A ι` is flat. The fibre conditions of the strata of Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–30, refined as in the Picard plan (index
`(φ, ψ, m, r)` with `r ≥ 1`), are bundled as values of `FiberCondition p` through
`FiberCondition.ofLineBundle`:

* `eulerCondition φ`: `C_φ`, `χ(X_t, L_t^{-1}(n)) = φ(n)` (`HasFiberDualEulerPolynomial`, (4.8.1));
* `baseCondition ψ`: `C_ψ`, `χ(X_t, O_{X_t}(n)) = ψ(n)` (`HasFiberStructureEulerPolynomial`);
* `levelCondition m r`: `C_{m,r}`, (4.8.3) for `n ≥ m` and `h^0(X_t, L_t(m)) = r`
  (`HasFiberTwistVanishingAndRank`);
* `coarseLevelCondition m`: `C_m`, (4.8.3) for `n ≥ m` and `h^0(X_t, L_t(m)) ≠ 0`
  (`HasFiberTwistVanishingAndSections`);
* `fineCondition φ ψ m r = C_φ ⊓ (C_ψ ⊓ C_{m,r})` and `coarseCondition φ m = C_φ ⊓ C_m`.

Their subsheaves `C.subfunctor` are the strata `Pic^φ`, `Pic^{φ,ψ,r}_m` and `Pic^φ_m`. For a
section `ξ` of `Pic_{X/S,(fppf)}` over a locally Noetherian `T`:

* the opens of `eulerCondition φ` and of `baseCondition ψ` are open and closed, pairwise
  disjoint, and cover `T` (`isClopen_setOf_holdsAt_eulerCondition`,
  `disjoint_opens_eulerCondition`, `iSup_opens_eulerCondition`, and the same for `ψ`; Kleiman
  p. 29: "the `T^φ` are disjoint and cover `T`");
* the opens of `coarseCondition φ m` increase with `m` (`opens_coarseCondition_mono`), and with
  geometrically integral fibres their union is the open of `eulerCondition φ`
  (`iSup_opens_coarseCondition`; p. 29, with the plan's nonvanishing condition);
* with geometrically integral fibres, the opens of `fineCondition φ ψ m (k + 1)` cover the open of
  `eulerCondition φ` over `(ψ, m, k)` (`iSup_opens_fineCondition_eq_eulerCondition`) and cover
  `T` over `(φ, ψ, m, k)` (`iSup_opens_fineCondition_eq_top`; the gluing index of the Picard
  plan); for fixed `m` they are pairwise disjoint (`disjoint_opens_fineCondition`);
* for fixed `(φ, m)`, with no integrality, the opens of `fineCondition φ ψ m (k + 1)` over
  `(ψ, k)` cover the open of `coarseCondition φ m` (`iSup_opens_fineCondition_eq_coarseCondition`).

If a representative `L` satisfies the fine condition at `m = 0` at every point of `T`, the
algebraically closed fibres of `X_T ⟶ T` have `h^0(L) = r` and no higher cohomology of `L`
(`fibreCohomologyConcentrated_of_forall_fineCondition_holds`), and for `T` locally Noetherian
the direct image of `L` is locally free of rank `r` and every base-change map of `L` is an
isomorphism (`sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds`): the
hypotheses of the representability of linear systems by Grassmannian bundles.

The base-change maps are those of `familyScheme p` (`familyBaseChange_eq_familyScheme_map`).
`twistClass i m T` is the class of `O_{X_T}(m)` (`fiberTwistClass`), equal to
`m • twistClass i 1 T` (`twistClass_eq_zsmul`) and natural in `T`
(`familyPicardFunctor_map_twistClass`), and translation by `m • twistClass i 1 T` carries the
conditions at `(φ, ψ, m, r)` to those at `(φ₀, ψ, 0, r)` with `φ₀(n) = φ(n − m)`
(`fineCondition_holds_add_twistClass`), the pointwise input of the twist isomorphism
`Pic^{φ,ψ,r}_m ≅ Pic^{φ₀,ψ,r}_0` (Kleiman p. 29, with the plan's correction of `φ(m + n)`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  (N : ℕ) (e : ι ≃ Fin (N + 1))

/-! ### The conditions -/

/-- **`C_φ`**: `χ(X_t, L_t^{-1}(n)) = φ(n)` for all `n` (Kleiman (4.8.1), arXiv:math/0504020v1,
p. 28); its subsheaf is `Pic^φ`. -/
def eulerCondition (φ : Polynomial ℚ) : FiberCondition (i ≫ toSpec A ι) :=
  FiberCondition.ofLineBundle (fun T L t => HasFiberDualEulerPolynomial i T.hom φ L t)
    (fun T _ _ ⟨e'⟩ t => hasFiberDualEulerPolynomial_congr i T.hom e' t φ)
    (fun g L t' => by
      have : Finite ι := Finite.of_equiv _ e.symm
      exact hasFiberDualEulerPolynomial_pullback_iff i _ _ g.left (Over.w g) L t' φ)
    (fun T hT L => by
      have := hT
      exact (isClopen_setOf_hasFiberDualEulerPolynomial i T.hom N e L φ).isOpen)

/-- **`C_ψ`**: `χ(X_t, O_{X_t}(n)) = ψ(n)` for all `n` (the base polynomial of the Picard plan;
Kleiman, arXiv:math/0504020v1, p. 30). It does not depend on the class. -/
def baseCondition (ψ : Polynomial ℚ) : FiberCondition (i ≫ toSpec A ι) :=
  FiberCondition.ofLineBundle (fun T _ t => HasFiberStructureEulerPolynomial i T.hom ψ t)
    (fun _ _ _ _ _ => Iff.rfl)
    (fun g _ t' => by
      have : Finite ι := Finite.of_equiv _ e.symm
      exact hasFiberStructureEulerPolynomial_pullback_iff i _ _ g.left (Over.w g) t' ψ)
    (fun T hT _ => by
      have := hT
      exact (isClopen_setOf_hasFiberStructureEulerPolynomial i T.hom N e ψ).isOpen)

/-- **`C_{m,r}`**: `H^q(X_t, L_t(n)) = 0` for `q ≥ 1`, `n ≥ m`, and `h^0(X_t, L_t(m)) = r`
(Picard plan; Kleiman (4.8.3), arXiv:math/0504020v1, p. 29). -/
def levelCondition (m : ℤ) (r : ℕ) : FiberCondition (i ≫ toSpec A ι) :=
  FiberCondition.ofLineBundle (fun T L t => HasFiberTwistVanishingAndRank i T.hom m r L t)
    (fun T _ _ ⟨e'⟩ t => hasFiberTwistVanishingAndRank_congr i T.hom e' t m r)
    (fun g L t' => by
      have : Finite ι := Finite.of_equiv _ e.symm
      exact hasFiberTwistVanishingAndRank_pullback_iff i _ _ g.left (Over.w g) L t' m r)
    (fun T hT L => by
      have := hT
      exact isOpen_setOf_hasFiberTwistVanishingAndRank i T.hom N e L m r)

/-- **`C_m`**: `H^q(X_t, L_t(n)) = 0` for `q ≥ 1`, `n ≥ m`, and `h^0(X_t, L_t(m)) ≠ 0` (Kleiman
(4.8.3), with the plan's nonvanishing condition). -/
def coarseLevelCondition (m : ℤ) : FiberCondition (i ≫ toSpec A ι) :=
  FiberCondition.ofLineBundle (fun T L t => HasFiberTwistVanishingAndSections i T.hom m L t)
    (fun T _ _ ⟨e'⟩ t => hasFiberTwistVanishingAndSections_congr i T.hom e' t m)
    (fun g L t' => by
      have : Finite ι := Finite.of_equiv _ e.symm
      exact hasFiberTwistVanishingAndSections_pullback_iff i _ _ g.left (Over.w g) L t' m)
    (fun T hT L => by
      have := hT
      exact isOpen_setOf_hasFiberTwistVanishingAndSections i T.hom N e L m)

/-- The condition of the fine stratum `Pic^{φ,ψ,r}_m`: `C_φ ⊓ (C_ψ ⊓ C_{m,r})`. -/
def fineCondition (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) : FiberCondition (i ≫ toSpec A ι) :=
  eulerCondition i N e φ ⊓ (baseCondition i N e ψ ⊓ levelCondition i N e m r)

/-- The condition of the coarse stratum `Pic^φ_m`: `C_φ ⊓ C_m`. -/
def coarseCondition (φ : Polynomial ℚ) (m : ℤ) : FiberCondition (i ≫ toSpec A ι) :=
  eulerCondition i N e φ ⊓ coarseLevelCondition i N e m

/-! ### The conditions on classes -/

variable {i N e}

theorem eulerCondition_holds_classOf (φ : Polynomial ℚ) (T : Over (Spec (.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (eulerCondition i N e φ).Holds T (classOf _ L) t ↔ HasFiberDualEulerPolynomial i T.hom φ L t :=
  Iff.rfl

theorem baseCondition_holds (ψ : Polynomial ℚ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (baseCondition i N e ψ).Holds T a t ↔ HasFiberStructureEulerPolynomial i T.hom ψ t := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact Iff.rfl

theorem levelCondition_holds_classOf (m : ℤ) (r : ℕ) (T : Over (Spec (.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (levelCondition i N e m r).Holds T (classOf _ L) t ↔
      HasFiberTwistVanishingAndRank i T.hom m r L t :=
  Iff.rfl

theorem coarseLevelCondition_holds_classOf (m : ℤ) (T : Over (Spec (.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (coarseLevelCondition i N e m).Holds T (classOf _ L) t ↔
      HasFiberTwistVanishingAndSections i T.hom m L t :=
  Iff.rfl

theorem fineCondition_holds_classOf (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) (T : Over (Spec (.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (fineCondition i N e φ ψ m r).Holds T (classOf _ L) t ↔
      HasFiberDualEulerPolynomial i T.hom φ L t ∧ HasFiberStructureEulerPolynomial i T.hom ψ t ∧
        HasFiberTwistVanishingAndRank i T.hom m r L t :=
  Iff.rfl

/-- The coarse condition is the fibre track's `IsFiberStratum`. -/
theorem coarseCondition_holds_classOf (φ : Polynomial ℚ) (m : ℤ) (T : Over (Spec (.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (coarseCondition i N e φ m).Holds T (classOf _ L) t ↔ IsFiberStratum i T.hom φ m L t :=
  Iff.rfl

/-- `C_ψ` at `t ∈ T` is `C_ψ` at the image of `t` in `Spec A`, for the trivial family. -/
theorem baseCondition_holds_iff_base (ψ : Polynomial ℚ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (baseCondition i N e ψ).Holds T a t ↔ HasFiberStructureEulerPolynomial i (𝟙 _) ψ (T.hom t) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact (baseCondition_holds ψ T a t).trans (hasFiberStructureEulerPolynomial_iff_base i T.hom ψ t)

/-- `C_m` holds exactly when `C_{m,r}` holds for some `r ≥ 1`. -/
theorem coarseLevelCondition_holds_iff_exists (m : ℤ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (coarseLevelCondition i N e m).Holds T a t ↔
      ∃ k : ℕ, (levelCondition i N e m (k + 1)).Holds T a t := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact hasFiberTwistVanishingAndSections_iff_exists i T.hom L t m

/-- Every point of every family satisfies `C_φ` for some `φ`. -/
theorem exists_eulerCondition_holds (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    ∃ φ : Polynomial ℚ, (eulerCondition i N e φ).Holds T a t := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact exists_hasFiberDualEulerPolynomial i T.hom L t N e

/-- `C_φ` holds for at most one `φ`. -/
theorem eq_of_eulerCondition_holds {φ φ' : Polynomial ℚ} {T : Over (Spec (.of A))}
    {a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)} {t : T.left}
    (h : (eulerCondition i N e φ).Holds T a t) (h' : (eulerCondition i N e φ').Holds T a t) :
    φ = φ' := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact HasFiberDualEulerPolynomial.unique i T.hom L t h h'

/-- Every point of every family satisfies `C_ψ` for some `ψ`. -/
theorem exists_baseCondition_holds (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    ∃ ψ : Polynomial ℚ, (baseCondition i N e ψ).Holds T a t := by
  obtain ⟨ψ, hψ⟩ := exists_hasFiberStructureEulerPolynomial i T.hom N e t
  exact ⟨ψ, (baseCondition_holds ψ T a t).mpr hψ⟩

/-- `C_ψ` holds for at most one `ψ`. -/
theorem eq_of_baseCondition_holds {ψ ψ' : Polynomial ℚ} {T : Over (Spec (.of A))}
    {a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)} {t : T.left}
    (h : (baseCondition i N e ψ).Holds T a t) (h' : (baseCondition i N e ψ').Holds T a t) :
    ψ = ψ' :=
  HasFiberStructureEulerPolynomial.unique i T.hom ((baseCondition_holds ψ T a t).mp h)
    ((baseCondition_holds ψ' T a t).mp h')

/-- `C_{m,r}` holds for at most one `r`. -/
theorem eq_of_levelCondition_holds {m : ℤ} {r r' : ℕ} {T : Over (Spec (.of A))}
    {a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)} {t : T.left}
    (h : (levelCondition i N e m r).Holds T a t) (h' : (levelCondition i N e m r').Holds T a t) :
    r = r' := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact HasFiberTwistVanishingAndRank.rank_eq i T.hom h h'

/-- With geometrically integral fibres, every point satisfies `C_{m,r}` with `r ≥ 1` for all
`m ≫ 0`. -/
theorem exists_forall_exists_levelCondition_holds [GeometricallyIntegral (i ≫ toSpec A ι)]
    (T : Over (Spec (.of A))) (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T))
    (t : T.left) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∃ k : ℕ, (levelCondition i N e m (k + 1)).Holds T a t := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact exists_forall_exists_hasFiberTwistVanishingAndRank i T.hom N e L t

/-- **The bridge on a family, degree `0`**: if a representative `L` satisfies the fine condition
at `m = 0` at every point of `T`, then `h^0(X_t, L_t) = r` at every point. -/
theorem modulePointFiberCohomologyDimension_zero_of_forall_fineCondition_holds
    {φ ψ : Polynomial ℚ} {r : ℕ} {T : Over (Spec (.of A))}
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (h : ∀ t, (fineCondition i N e φ ψ 0 r).Holds T (classOf _ L) t) (t : T.left) :
    modulePointFiberCohomologyDimension (pullback.snd (i ≫ toSpec A ι) T.hom) L.val 0 t = r :=
  (h t).2.2.modulePointFiberCohomologyDimension_zero i T.hom

/-- **The bridge on a family, positive degrees**: if a representative `L` satisfies the fine
condition at `m = 0` at every point of `T`, then the point-fibre cohomology of `L` vanishes in
every positive degree at every point. -/
theorem subsingleton_modulePointFiberCohomology_of_forall_fineCondition_holds
    {φ ψ : Polynomial ℚ} {r : ℕ} {T : Over (Spec (.of A))}
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (h : ∀ t, (fineCondition i N e φ ψ 0 r).Holds T (classOf _ L) t) (t : T.left) {q : ℕ}
    (hq : 0 < q) :
    Subsingleton (modulePointFiberCohomology (pullback.snd (i ≫ toSpec A ι) T.hom) L.val q t) :=
  (h t).2.2.subsingleton_modulePointFiberCohomology i T.hom N e hq

/-- **Geometric fibre concentration on a fine stratum at `m = 0`**: if a representative `L`
satisfies the fine condition at `m = 0` at every point of `T`, then every algebraically closed
fibre of `X_T ⟶ T` has `h^0(L) = r` and no higher cohomology of `L`. -/
theorem fibreCohomologyConcentrated_of_forall_fineCondition_holds {φ ψ : Polynomial ℚ} {r : ℕ}
    {T : Over (Spec (.of A))} {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (h : ∀ t, (fineCondition i N e φ ψ 0 r).Holds T (classOf _ L) t) :
    FibreCohomologyConcentrated (pullback.snd (i ≫ toSpec A ι) T.hom) L.val r := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact fibreCohomologyConcentrated_of_modulePointFiberCohomology _ L.val r
    (modulePointFiberCohomologyDimension_zero_of_forall_fineCondition_holds h)
    (fun t _ hq => subsingleton_modulePointFiberCohomology_of_forall_fineCondition_holds h t hq)

/-- **The direct image on a fine stratum at `m = 0`** (Picard plan, statement 15a): over a
locally Noetherian `T`, if a representative `L` satisfies the fine condition at `m = 0` at every
point of `T`, then `p_* L` is locally free of rank `r` and every base-change map of `L` is an
isomorphism. These are the hypotheses `hE` (with `r = k + 1`) and `hbc` of the representability of
linear systems by Grassmannian bundles. -/
theorem sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds
    {φ ψ : Polynomial ℚ} {r : ℕ} {T : Over (Spec (.of A))} [IsLocallyNoetherian T.left]
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (h : ∀ t, (fineCondition i N e φ ψ 0 r).Holds T (classOf _ L) t) :
    Modules.SheafHasRank ((Modules.pushforward (pullback.snd (i ≫ toSpec A ι) T.hom)).obj L.val)
        r ∧
      ∀ (T' : Scheme.{u}) (g : T' ⟶ T.left),
        IsIso (Modules.moduleBaseChangeMap (pullback.snd (i ≫ toSpec A ι) T.hom) g L.val) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have := lineBundle_isLocallyFree _ L
  have := lineBundle_isFinitePresentation _ L
  exact localFreeCohomologyBaseChange_of_isLocallyNoetherian _ L.val r
    (fibreCohomologyConcentrated_of_forall_fineCondition_holds h)

/-! ### Covers -/

section Covers

variable {T : Over (Spec (.of A))} [IsLocallyNoetherian T.left]
  (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T))

/-- **The opens of `C_φ` cover `T`** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem iSup_opens_eulerCondition : ⨆ φ, (eulerCondition i N e φ).opens ξ = ⊤ :=
  FiberCondition.iSup_opens_eq_top _ (fun T a t => exists_eulerCondition_holds T a t) ξ

/-- **The opens of `C_φ` are pairwise disjoint** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem disjoint_opens_eulerCondition {φ φ' : Polynomial ℚ} (h : φ ≠ φ') :
    Disjoint ((eulerCondition i N e φ).opens ξ) ((eulerCondition i N e φ').opens ξ) :=
  (eulerCondition i N e φ).disjoint_opens (fun _ _ _ hC hD => h (eq_of_eulerCondition_holds hC hD))
    ξ

/-- **The opens of `C_φ` are open and closed.** -/
theorem isClopen_setOf_holdsAt_eulerCondition (φ : Polynomial ℚ) :
    IsClopen {t : T.left | (eulerCondition i N e φ).HoldsAt ξ t} :=
  (eulerCondition i N e φ).isClopen_setOf_holdsAt_of_isClosed (fun T hT a => by
    have := hT
    obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
    exact (isClopen_setOf_hasFiberDualEulerPolynomial i T.hom N e L φ).isClosed) ξ

/-- **The opens of `C_ψ` cover `T`.** -/
theorem iSup_opens_baseCondition : ⨆ ψ, (baseCondition i N e ψ).opens ξ = ⊤ :=
  FiberCondition.iSup_opens_eq_top _ (fun T a t => exists_baseCondition_holds T a t) ξ

/-- **The opens of `C_ψ` are pairwise disjoint.** -/
theorem disjoint_opens_baseCondition {ψ ψ' : Polynomial ℚ} (h : ψ ≠ ψ') :
    Disjoint ((baseCondition i N e ψ).opens ξ) ((baseCondition i N e ψ').opens ξ) :=
  (baseCondition i N e ψ).disjoint_opens (fun _ _ _ hC hD => h (eq_of_baseCondition_holds hC hD))
    ξ

/-- **The opens of `C_ψ` are open and closed.** -/
theorem isClopen_setOf_holdsAt_baseCondition (ψ : Polynomial ℚ) :
    IsClopen {t : T.left | (baseCondition i N e ψ).HoldsAt ξ t} :=
  (baseCondition i N e ψ).isClopen_setOf_holdsAt_of_isClosed (fun T hT a => by
    have := hT
    simp only [baseCondition_holds]
    exact (isClopen_setOf_hasFiberStructureEulerPolynomial i T.hom N e ψ).isClosed) ξ

/-- **The coarse strata increase with `m`** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem opens_coarseCondition_mono (φ : Polynomial ℚ) {m m' : ℤ} (h : m ≤ m') :
    (coarseCondition i N e φ m).opens ξ ≤ (coarseCondition i N e φ m').opens ξ :=
  (coarseCondition i N e φ m).opens_mono (fun T a t hc => by
    obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
    exact ⟨hc.1, hc.2.mono i T.hom L t N e h⟩) ξ

/-- **The coarse strata cover `Pic^φ`** (Kleiman, arXiv:math/0504020v1, p. 29, with the
plan's nonvanishing condition): with geometrically integral fibres, the union over `m` of the
opens of `C_φ ⊓ C_m` is the open of `C_φ`. -/
theorem iSup_opens_coarseCondition [GeometricallyIntegral (i ≫ toSpec A ι)] (φ : Polynomial ℚ) :
    ⨆ m, (coarseCondition i N e φ m).opens ξ = (eulerCondition i N e φ).opens ξ :=
  (eulerCondition i N e φ).iSup_opens_inf_eq (fun m => coarseLevelCondition i N e m)
    (fun T a t _ => by
      obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
      obtain ⟨m₀, hm₀⟩ := exists_forall_hasFiberTwistVanishingAndSections i T.hom L t N e
      exact ⟨m₀, hm₀ m₀ le_rfl⟩) ξ

/-- **The fine strata cover `Pic^φ`** (refined by the base polynomial and the rank): with
geometrically integral
fibres, the union over `(ψ, m, k)` of the opens of `fineCondition φ ψ m (k + 1)` is the open of
`C_φ`. -/
theorem iSup_opens_fineCondition_eq_eulerCondition [GeometricallyIntegral (i ≫ toSpec A ι)]
    (φ : Polynomial ℚ) :
    ⨆ x : Polynomial ℚ × ℤ × ℕ, (fineCondition i N e φ x.1 x.2.1 (x.2.2 + 1)).opens ξ =
      (eulerCondition i N e φ).opens ξ :=
  (eulerCondition i N e φ).iSup_opens_inf_eq
    (fun x : Polynomial ℚ × ℤ × ℕ =>
      baseCondition i N e x.1 ⊓ levelCondition i N e x.2.1 (x.2.2 + 1))
    (fun T a t _ => by
      obtain ⟨ψ, hψ⟩ := exists_baseCondition_holds (N := N) (e := e) T a t
      obtain ⟨m₀, hm₀⟩ := exists_forall_exists_levelCondition_holds (N := N) (e := e) T a t
      obtain ⟨k, hk⟩ := hm₀ m₀ le_rfl
      exact ⟨(ψ, m₀, k), hψ, hk⟩) ξ

/-- **The fine strata cover `T`** (the gluing index of the Picard plan: `(φ, ψ, m, k)` with
`r = k + 1`). -/
theorem iSup_opens_fineCondition_eq_top [GeometricallyIntegral (i ≫ toSpec A ι)] :
    ⨆ x : Polynomial ℚ × Polynomial ℚ × ℤ × ℕ,
      (fineCondition i N e x.1 x.2.1 x.2.2.1 (x.2.2.2 + 1)).opens ξ = ⊤ :=
  FiberCondition.iSup_opens_eq_top _ (fun T a t => by
    obtain ⟨φ, hφ⟩ := exists_eulerCondition_holds (N := N) (e := e) T a t
    obtain ⟨ψ, hψ⟩ := exists_baseCondition_holds (N := N) (e := e) T a t
    obtain ⟨m₀, hm₀⟩ := exists_forall_exists_levelCondition_holds (N := N) (e := e) T a t
    obtain ⟨k, hk⟩ := hm₀ m₀ le_rfl
    exact ⟨(φ, ψ, m₀, k), hφ, hψ, hk⟩) ξ

/-- A fine stratum with `r ≠ 0` lies in the coarse stratum. -/
theorem opens_fineCondition_le_coarseCondition (φ ψ : Polynomial ℚ) (m : ℤ) {r : ℕ}
    (hr : r ≠ 0) :
    (fineCondition i N e φ ψ m r).opens ξ ≤ (coarseCondition i N e φ m).opens ξ :=
  (fineCondition i N e φ ψ m r).opens_mono (fun T a t h => by
    obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
    exact ⟨h.1, h.2.2.hasFiberTwistVanishingAndSections i T.hom hr⟩) ξ

/-- **For fixed `(φ, m)`, the fine strata cover the coarse stratum**: the union over `(ψ, k)` of
the opens of `fineCondition φ ψ m (k + 1)` is the open of `C_φ ⊓ C_m`. No integrality is
needed. -/
theorem iSup_opens_fineCondition_eq_coarseCondition (φ : Polynomial ℚ) (m : ℤ) :
    ⨆ x : Polynomial ℚ × ℕ, (fineCondition i N e φ x.1 m (x.2 + 1)).opens ξ =
      (coarseCondition i N e φ m).opens ξ := by
  apply le_antisymm
  · exact iSup_le fun x => opens_fineCondition_le_coarseCondition ξ φ x.1 m (Nat.succ_ne_zero _)
  · refine ((coarseCondition i N e φ m).iSup_opens_inf_eq
      (fun x : Polynomial ℚ × ℕ => fineCondition i N e φ x.1 m (x.2 + 1))
      (fun T a t hc => ?_) ξ).symm.le.trans
      (iSup_mono fun x => ((coarseCondition i N e φ m).opens_inf _ ξ).le.trans inf_le_right)
    obtain ⟨ψ, hψ⟩ := exists_baseCondition_holds (N := N) (e := e) T a t
    obtain ⟨k, hk⟩ := (coarseLevelCondition_holds_iff_exists (N := N) (e := e) m T a t).mp hc.2
    exact ⟨(ψ, k), hc.1, hψ, hk⟩

/-- **For fixed `m`, the fine strata are pairwise disjoint.** -/
theorem disjoint_opens_fineCondition {φ φ' ψ ψ' : Polynomial ℚ} {m : ℤ} {r r' : ℕ}
    (h : (φ, ψ, r) ≠ (φ', ψ', r')) :
    Disjoint ((fineCondition i N e φ ψ m r).opens ξ) ((fineCondition i N e φ' ψ' m r').opens ξ) :=
  (fineCondition i N e φ ψ m r).disjoint_opens (fun _ _ _ hC hD => h (by
    rw [eq_of_eulerCondition_holds hC.1 hD.1, eq_of_baseCondition_holds hC.2.1 hD.2.1,
      eq_of_levelCondition_holds hC.2.2 hD.2.2])) ξ

end Covers

/-! ### The twisting class -/

variable (i)

omit [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] in
/-- The class `o_T(m)` of `O_{X_T}(m)` in `Pic(X_T)` (`fiberTwistClass`), as a section of the
family Picard functor. -/
abbrev twistClass (m : ℤ) (T : Over (Spec (.of A))) :
    (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T) :=
  fiberTwistClass i T.hom m

omit [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] in
/-- `o_T(m) = m • o_T(1)`. -/
theorem twistClass_eq_zsmul (m : ℤ) (T : Over (Spec (.of A))) :
    twistClass i m T = m • twistClass i 1 T :=
  fiberTwistClass_eq_zsmul i T.hom m

omit [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] in
/-- **The twisting classes are natural**: `g^* o_T(m) = o_{T'}(m)`. -/
theorem familyPicardFunctor_map_twistClass {T T' : Over (Spec (.of A))} (g : T' ⟶ T) (m : ℤ) :
    ((familyPicardFunctor (i ≫ toSpec A ι)).map g.op).hom (twistClass i m T) =
      twistClass i m T' := by
  rw [familyPicardFunctor_map_apply]
  exact pullbackClass_familyBaseChange_fiberTwistClass i T.hom T'.hom g.left (Over.w g) m

variable {i}

omit [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] in
/-- If `a` is the class of `L`, then `a + m • o_T(1)` is the class of `L(m)`. -/
theorem add_zsmul_twistClass_eq_classOf {T : Over (Spec (.of A))}
    {a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)}
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)} (ha : classOf _ L = a) (m : ℤ) :
    a + m • twistClass i 1 T = classOf _ (pulledTwistLineBundle i T.hom m L) := by
  subst ha
  exact (classOf_pulledTwistLineBundle i T.hom m L).symm

/-- **Translation by `m • o_T(1)` shifts `C_{m,r}`**: `C_{m',r}` at `a + m • o_T(1)` is
`C_{m'+m,r}` at `a`. -/
theorem levelCondition_holds_add_twistClass (m' m : ℤ) (r : ℕ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (levelCondition i N e m' r).Holds T (a + m • twistClass i 1 T) t ↔
      (levelCondition i N e (m' + m) r).Holds T a t := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (a : PicardGroup _)
  rw [add_zsmul_twistClass_eq_classOf hL, ← hL]
  exact hasFiberTwistVanishingAndRank_pulledTwistLineBundle_iff i T.hom L t m' m r

/-- **Translation by `m • o_T(1)` carries `C_φ` to `C_{φ₀}`**, `φ₀(n) = φ(n − m)`. -/
theorem eulerCondition_holds_add_twistClass (φ : Polynomial ℚ) (m : ℤ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (eulerCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ)))).Holds T
        (a + m • twistClass i 1 T) t ↔ (eulerCondition i N e φ).Holds T a t := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (a : PicardGroup _)
  rw [add_zsmul_twistClass_eq_classOf hL, ← hL]
  exact hasFiberDualEulerPolynomial_pulledTwistLineBundle_iff i T.hom L t φ m

/-- **Translation by `m • o_T(1)` carries the fine stratum at `(φ, ψ, m, r)` to the one at
`(φ₀, ψ, 0, r)`**, `φ₀(n) = φ(n − m)`: the pointwise form of `Pic^{φ,ψ,r}_m ≅ Pic^{φ₀,ψ,r}_0`
(Kleiman, arXiv:math/0504020v1, pp. 29–30, with the plan's correction of `φ(m + n)`). -/
theorem fineCondition_holds_add_twistClass (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ)
    (T : Over (Spec (.of A))) (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T))
    (t : T.left) :
    (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0 r).Holds T
        (a + m • twistClass i 1 T) t ↔ (fineCondition i N e φ ψ m r).Holds T a t := by
  rw [fineCondition, fineCondition, FiberCondition.inf_holds, FiberCondition.inf_holds,
    FiberCondition.inf_holds, FiberCondition.inf_holds, eulerCondition_holds_add_twistClass,
    baseCondition_holds, baseCondition_holds, levelCondition_holds_add_twistClass, zero_add]

end AlgebraicGeometry.Scheme.RelativePicard.Strata
