/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Strata.Conditions

/-! Focused consumer of the strata bundle of the Picard functor (Kleiman, arXiv:math/0504020v1,
proof of Thm 4.8, pp. 28–30, with the plan's refinement by the base polynomial and the rank and
its gluing index): the zero twist and the point-fibre bridge at `m = 0`, the base polynomial `C_ψ`
and the level condition `C_{m,r}`, the conditions as `FiberCondition` values with their strata,
the covers, the direct image on a fine stratum, and the twisting class, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-! ### The pointwise conditions -/

section Pointwise

variable {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of A))

/-- `C_ψ` is the Euler polynomial of the structure sheaf of the fibre, with no hypothesis on `A`. -/
example (ψ : ℚ[X]) (t : T) :
    HasFiberStructureEulerPolynomial i s ψ t ↔ ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ s)
        (SheafOfModules.unit _) n : ℚ) = ψ.eval (n : ℚ) := by
  simp only [HasFiberStructureEulerPolynomial, fiberStructureEulerChar_eq]

/-- `C_ψ` at a point of `T` is `C_ψ` at its image in `Spec A`. -/
example [IsProper (i ≫ toSpec A ι)] (ψ : ℚ[X]) (t : T) :
    HasFiberStructureEulerPolynomial i s ψ t ↔
      HasFiberStructureEulerPolynomial i (𝟙 _) ψ (s t) :=
  hasFiberStructureEulerPolynomial_iff_base i s ψ t

/-- Over a Noetherian `A`, only finitely many base polynomials occur. -/
example [IsNoetherianRing A] [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) :
    {ψ : ℚ[X] | ∃ s : Spec (CommRingCat.of A),
      HasFiberStructureEulerPolynomial i (𝟙 (Spec (CommRingCat.of A))) ψ s}.Finite :=
  finite_setOf_exists_hasFiberStructureEulerPolynomial i N e

/-- `C_{m,r}` is vanishing (4.8.3) for `n ≥ m` and `h^0(X_t, L_t(m)) = r`. -/
example (m : ℤ) (r : ℕ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    HasFiberTwistVanishingAndRank i s m r L t ↔
      (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n → fiberTwistDim i s L t n q = 0) ∧
        fiberTwistDim i s L t m 0 = r :=
  Iff.rfl

/-- `C_m` is `C_{m,r}` for some `r ≥ 1`. -/
example (m : ℤ) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) :
    HasFiberTwistVanishingAndSections i s m L t ↔
      ∃ k : ℕ, HasFiberTwistVanishingAndRank i s m (k + 1) L t :=
  hasFiberTwistVanishingAndSections_iff_exists i s L t m

/-- **Openness of `C_{m,r}`** on a locally Noetherian base. -/
example [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] [IsLocallyNoetherian T] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (m : ℤ) (r : ℕ) :
    IsOpen {t : T | HasFiberTwistVanishingAndRank i s m r L t} :=
  isOpen_setOf_hasFiberTwistVanishingAndRank i s N e L m r

/-- **Clopenness of `C_ψ`** on a locally Noetherian base. -/
example [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] [IsLocallyNoetherian T] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (ψ : ℚ[X]) :
    IsClopen {t : T | HasFiberStructureEulerPolynomial i s ψ t} :=
  isClopen_setOf_hasFiberStructureEulerPolynomial i s N e ψ

/-- The twist `L ↦ L(m)` shifts `C_{m',r}` to `C_{m'+m,r}`. -/
example [IsClosedImmersion i] (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T)
    (m' m : ℤ) (r : ℕ) :
    HasFiberTwistVanishingAndRank i s m' r (pulledTwistLineBundle i s m L) t ↔
      HasFiberTwistVanishingAndRank i s (m' + m) r L t :=
  hasFiberTwistVanishingAndRank_pulledTwistLineBundle_iff i s L t m' m r

/-! ### The zero twist and the bridge to cohomology and base change -/

/-- The zero twist is the identity. -/
example {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι) (M : Y.Modules) : pulledTwist h 0 M ≅ M :=
  pulledTwistZeroIso h M

/-- **The bridge**: at a point where `C_{0,r}` holds, `h^0(X_t, L_t) = r` and the higher
point-fibre cohomology of `L` vanishes, which are the point-fibre hypotheses of cohomology and
base change. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (r : ℕ)
    (h : HasFiberTwistVanishingAndRank i s 0 r L t) :
    modulePointFiberCohomologyDimension (pullback.snd (i ≫ toSpec A ι) s) L.val 0 t = r ∧
      ∀ q : ℕ, 0 < q →
        Subsingleton (modulePointFiberCohomology (pullback.snd (i ≫ toSpec A ι) s) L.val q t) :=
  ⟨h.modulePointFiberCohomologyDimension_zero i s,
    fun _ hq => h.subsingleton_modulePointFiberCohomology i s N e hq⟩

end Pointwise

/-! ### The conditions and their strata -/

section Conditions

variable [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))

/-- The fine condition on a class is `C_φ ∧ C_ψ ∧ C_{m,r}` on a representative. -/
example (φ ψ : ℚ[X]) (m : ℤ) (r : ℕ) (T : Over (Spec (CommRingCat.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (fineCondition i N e φ ψ m r).Holds T (classOf _ L) t ↔
      HasFiberDualEulerPolynomial i T.hom φ L t ∧ HasFiberStructureEulerPolynomial i T.hom ψ t ∧
        HasFiberTwistVanishingAndRank i T.hom m r L t :=
  Iff.rfl

/-- The coarse condition on a class is the fibre track's `IsFiberStratum`. -/
example (φ : ℚ[X]) (m : ℤ) (T : Over (Spec (CommRingCat.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (coarseCondition i N e φ m).Holds T (classOf _ L) t ↔ IsFiberStratum i T.hom φ m L t :=
  Iff.rfl

/-- The fine stratum `Pic^{φ,ψ,r}_m` is an fppf subsheaf of `Pic_{X/S,(fppf)}`. -/
example (φ ψ : ℚ[X]) (m : ℤ) (r : ℕ) :
    Presieve.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of A)))
      (fineCondition i N e φ ψ m r).subfunctor.toFunctor :=
  (fineCondition i N e φ ψ m r).isSheaf_subfunctor

/-- A class over `T` lies in `Pic^{φ,ψ,r}_m` exactly when every point of `T` satisfies the fine
condition. -/
example (φ ψ : ℚ[X]) (m : ℤ) (r : ℕ) (T : Over (Spec (CommRingCat.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) :
    (quotientProjection _ ≫ toFppfPicardSheaf _).app (op T) a ∈
        (fineCondition i N e φ ψ m r).subfunctor.obj (op T) ↔
      ∀ t : T.left, (fineCondition i N e φ ψ m r).Holds T a t :=
  (fineCondition i N e φ ψ m r).app_mem_subfunctor_iff a

/-- **The bridge on a family**: the fine condition at `m = 0` at every point gives the point-fibre
hypotheses of cohomology and base change for a representative, and geometric fibre
concentration. -/
example {φ ψ : ℚ[X]} {r : ℕ} {T : Over (Spec (CommRingCat.of A))}
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (h : ∀ t, (fineCondition i N e φ ψ 0 r).Holds T (classOf _ L) t) (t : T.left) (q : ℕ)
    (hq : 0 < q) :
    modulePointFiberCohomologyDimension (pullback.snd (i ≫ toSpec A ι) T.hom) L.val 0 t = r ∧
      Subsingleton (modulePointFiberCohomology (pullback.snd (i ≫ toSpec A ι) T.hom) L.val q t) ∧
      FibreCohomologyConcentrated (pullback.snd (i ≫ toSpec A ι) T.hom) L.val r :=
  ⟨modulePointFiberCohomologyDimension_zero_of_forall_fineCondition_holds h t,
    subsingleton_modulePointFiberCohomology_of_forall_fineCondition_holds h t hq,
    fibreCohomologyConcentrated_of_forall_fineCondition_holds h⟩

/-- **The direct image on a fine stratum at `m = 0`**, over a locally Noetherian `T`: `p_* L` is
locally free of rank `k + 1` and every base-change map of `L` is an isomorphism, in the form of
the hypotheses `hE` and `hbc` of the representability of linear systems. -/
example {φ ψ : ℚ[X]} {k : ℕ} {T : Over (Spec (CommRingCat.of A))} [IsLocallyNoetherian T.left]
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (h : ∀ t, (fineCondition i N e φ ψ 0 (k + 1)).Holds T (classOf _ L) t) :
    (∀ (T' : Scheme.{u}) (g : T' ⟶ T.left),
        IsIso (Scheme.Modules.moduleBaseChangeMap (pullback.snd (i ≫ toSpec A ι) T.hom) g
          L.val)) ∧
      Scheme.Modules.SheafHasRank
        ((Scheme.Modules.pushforward (pullback.snd (i ≫ toSpec A ι) T.hom)).obj L.val) (k + 1) :=
  ⟨(sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds h).2,
    (sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds h).1⟩

variable {T : Over (Spec (CommRingCat.of A))} [IsLocallyNoetherian T.left]
  (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T))

/-- The `C_φ`-opens and the `C_ψ`-opens are clopen, disjoint and cover `T`. -/
example (φ φ' ψ ψ' : ℚ[X]) (hφ : φ ≠ φ') (hψ : ψ ≠ ψ') :
    IsClopen {t : T.left | (eulerCondition i N e φ).HoldsAt ξ t} ∧
      Disjoint ((eulerCondition i N e φ).opens ξ) ((eulerCondition i N e φ').opens ξ) ∧
      ⨆ φ, (eulerCondition i N e φ).opens ξ = ⊤ ∧
      IsClopen {t : T.left | (baseCondition i N e ψ).HoldsAt ξ t} ∧
      Disjoint ((baseCondition i N e ψ).opens ξ) ((baseCondition i N e ψ').opens ξ) ∧
      ⨆ ψ, (baseCondition i N e ψ).opens ξ = ⊤ :=
  ⟨isClopen_setOf_holdsAt_eulerCondition ξ φ, disjoint_opens_eulerCondition ξ hφ,
    iSup_opens_eulerCondition ξ, isClopen_setOf_holdsAt_baseCondition ξ ψ,
    disjoint_opens_baseCondition ξ hψ, iSup_opens_baseCondition ξ⟩

/-- The coarse strata are nested and, with geometrically integral fibres, exhaust `Pic^φ`. -/
example [GeometricallyIntegral (i ≫ toSpec A ι)] (φ : ℚ[X]) {m m' : ℤ} (h : m ≤ m') :
    (coarseCondition i N e φ m).opens ξ ≤ (coarseCondition i N e φ m').opens ξ ∧
      ⨆ m, (coarseCondition i N e φ m).opens ξ = (eulerCondition i N e φ).opens ξ :=
  ⟨opens_coarseCondition_mono ξ φ h, iSup_opens_coarseCondition ξ φ⟩

/-- **The fine strata**: for fixed `(φ, m)` they cover the coarse stratum; with geometrically
integral fibres they cover `T` over the gluing index `(φ, ψ, m, k)`, `r = k + 1`; for fixed `m`
they are pairwise disjoint. -/
example [GeometricallyIntegral (i ≫ toSpec A ι)] (φ : ℚ[X]) (m : ℤ) :
    ⨆ x : ℚ[X] × ℕ, (fineCondition i N e φ x.1 m (x.2 + 1)).opens ξ =
        (coarseCondition i N e φ m).opens ξ ∧
      ⨆ x : ℚ[X] × ℚ[X] × ℤ × ℕ,
        (fineCondition i N e x.1 x.2.1 x.2.2.1 (x.2.2.2 + 1)).opens ξ = ⊤ :=
  ⟨iSup_opens_fineCondition_eq_coarseCondition ξ φ m, iSup_opens_fineCondition_eq_top ξ⟩

example {φ φ' ψ ψ' : ℚ[X]} {m : ℤ} {r r' : ℕ} (h : (φ, ψ, r) ≠ (φ', ψ', r')) :
    Disjoint ((fineCondition i N e φ ψ m r).opens ξ) ((fineCondition i N e φ' ψ' m r').opens ξ) :=
  disjoint_opens_fineCondition ξ h

end Conditions

/-! ### The twisting class -/

/-- The twisting class is the class of `O_{X_T}(m)`, equal to `m • o_T(1)` and natural in `T`. -/
example (m : ℤ) {T T' : Over (Spec (CommRingCat.of A))} (g : T' ⟶ T) :
    twistClass i m T = m • twistClass i 1 T ∧
      ((familyPicardFunctor (i ≫ toSpec A ι)).map g.op).hom (twistClass i m T) =
        twistClass i m T' :=
  ⟨twistClass_eq_zsmul i m T, familyPicardFunctor_map_twistClass i g m⟩

/-- **Translation by `m • o_T(1)`** carries the fine condition at `(φ, ψ, m, r)` to the one at
`(φ₀, ψ, 0, r)`, `φ₀(n) = φ(n - m)`. -/
example [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (φ ψ : ℚ[X]) (m : ℤ) (r : ℕ) (T : Over (Spec (CommRingCat.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0 r).Holds T
        (a + m • twistClass i 1 T) t ↔ (fineCondition i N e φ ψ m r).Holds T a t :=
  fineCondition_holds_add_twistClass φ ψ m r T a t

/-! ### Axiom guards -/

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_modulePointFiberCohomology_iff_embeddedFiberTwistDim_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subsingleton_modulePointFiberCohomology_iff_embeddedFiberTwistDim_zero

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isClopen_setOf_hasFiberStructureEulerPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClopen_setOf_hasFiberStructureEulerPolynomial

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.hasFiberStructureEulerPolynomial_pullback_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hasFiberStructureEulerPolynomial_pullback_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.finite_setOf_exists_hasFiberStructureEulerPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_setOf_exists_hasFiberStructureEulerPolynomial

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isOpen_setOf_hasFiberTwistVanishingAndRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isOpen_setOf_hasFiberTwistVanishingAndRank

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_forall_exists_hasFiberTwistVanishingAndRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_forall_exists_hasFiberTwistVanishingAndRank

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.HasFiberTwistVanishingAndRank.modulePointFiberCohomologyDimension_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms HasFiberTwistVanishingAndRank.modulePointFiberCohomologyDimension_zero

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.HasFiberTwistVanishingAndRank.subsingleton_modulePointFiberCohomology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms HasFiberTwistVanishingAndRank.subsingleton_modulePointFiberCohomology

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.iSup_opens_inf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.iSup_opens_inf_eq

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fineCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fibreCohomologyConcentrated_of_forall_fineCondition_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fibreCohomologyConcentrated_of_forall_fineCondition_holds

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isClopen_setOf_holdsAt_baseCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClopen_setOf_holdsAt_baseCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.iSup_opens_coarseCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms iSup_opens_coarseCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.iSup_opens_fineCondition_eq_coarseCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms iSup_opens_fineCondition_eq_coarseCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.iSup_opens_fineCondition_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms iSup_opens_fineCondition_eq_top

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.disjoint_opens_fineCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms disjoint_opens_fineCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.twistClass_eq_zsmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twistClass_eq_zsmul

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.familyPicardFunctor_map_twistClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyPicardFunctor_map_twistClass

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fineCondition_holds_add_twistClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineCondition_holds_add_twistClass
