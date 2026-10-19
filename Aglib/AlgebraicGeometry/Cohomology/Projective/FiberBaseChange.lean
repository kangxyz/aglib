/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Transitivity
public import Aglib.AlgebraicGeometry.Cohomology.Projective.BaseChangeComparison
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Finiteness

/-!
# Large twists of a coherent sheaf: vanishing and base change on every fibre

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)` and `F` a coherent module on `P^n_A`, flat or
not. This file proves statements (B) and (C) of the proof of Nitsure, *Construction of Hilbert
and Quot schemes*, arXiv:math/0504590v1, Thm 4.3, p. 21, over the affine base `S = Spec A`:

* (B) (`exists_twist_vanishing_and_fiber_vanishing`): there is `N₁` such that for every
  `m ≥ N₁` the cohomology `H^r(P^n_A, F(m))` vanishes for `r ≥ 1` (on the affine base this is
  `R^r π_* F(m) = 0`), and `H^r(P^n_s, F_s(m)) = 0` for `r ≥ 1` and every `s ∈ Spec A`;
* (C) (`exists_twist_vanishing_and_fiber_baseChange_isIso`): there is `N` such that for every
  `m ≥ N` the statements of (B) hold and the base-change map
  `κ(s) ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(P^n_s, F_s(m))` is an isomorphism for every `s ∈ Spec A`.

`exists_twist_fiber_vanishing_and_bijective_projectiveSpace` restates both on `P^n_{κ(s)}`, with
the twists `𝒪(m) ⊗ F_s` there, in the form of the fibre hypotheses of
`bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace` (`BaseChangeComparison`).

Here `F(m) = 𝒪(m) ⊗ F`, the fibre `P^n_s` is the native fibre product
`P^n_A ×_{Spec A} Spec κ(s)`, `F_s(m)` is the pullback of `F(m)` along its first projection, and
the base-change map is `moduleCohomologyBaseChangeMap`, as in `FlatTwist` and
`LargeTwistBaseChange`; on the affine base `(π_* F(m))|_s = κ(s) ⊗_A H^0(P^n_A, F(m))`.

The proof is Nitsure's, with his finite stratification replaced by Noetherian induction on
`Spec A` (`TopologicalSpace.NoetherianSpace.exists_forall_le_of_isIrreducible`, from
`finite_range_of_isIrreducible`), as in `HilbertPolynomial/Finiteness`. At an irreducible closed
`Z = V(p)`, generic flatness gives `a ≠ 0` in `A ⧸ p` such that `F` becomes flat over the
Noetherian ring `B = (A ⧸ p)_a` (`exists_ne_zero_relativeFlat_pullback_away`). For `σ : A → B`:

* Lemma 3.1 (`exists_twist_baseChange_isIso_of_isNoetherianRing`) gives, for large `m`, the
  base-change isomorphism `B ⊗_A H^0(F(m)) ≅ H^0(F(m)_B)` and the vanishing of the positive
  cohomology of `F(m)_B`;
* the flat family `F(m)_B` then has base change in every degree and vanishing positive fibre
  cohomology after every ring map `ψ : B → C` (`VanishingProjective`);
* transitivity of base change (`moduleCohomologyBaseChangeMap_isIso_comp`) and the fibre
  comparison `(X_B)_C ≅ X_C` (`baseChangeTransCohomologyHom`) give (B) and (C) for `ψ ∘ σ`
  (`exists_twist_fiber_baseChange_of_relativeFlat_map`).

Every point `s ∈ V(p) ∩ D(g)`, `g` a lift of `a`, has `A → κ(s)` factoring through `B`; this is
the local step `exists_basicOpen_twist_fiber_baseChange`. The bound of Lemma 3.1 depends on `σ`,
and the induction needs one such bound on a nonempty open part of each irreducible closed subset;
the uniform bound comes from the finite range of the pointwise least bounds.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u}

/-- **Base change through a Noetherian ring over which `F` becomes flat** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, (B) and (C) on one flat piece `V_i`, p. 21): let
`σ : A →+* B` be a ring map to a Noetherian ring such that `π^* F` is flat over `B` on `P^n_B`.
There is a bound `N` such that for every `d ≥ N` and every ring map `ρ = ψ ∘ σ` with
`ψ : B →+* C`, the base change of `F(d)` along `ρ` has vanishing positive cohomology, and its
degree-zero base-change map is an isomorphism. -/
theorem exists_twist_fiber_baseChange_of_relativeFlat_map (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B)
    (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d → ∀ (C : Type u) [CommRing C] (ψ : B →+* C) (ρ : A →+* C),
      ψ.comp σ = ρ →
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom ρ)))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom ρ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q)) ∧
      IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) ρ
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨N, hN⟩ := exists_twist_baseChange_isIso_of_isNoetherianRing n e F hF σ
  refine ⟨N, fun d hd C _ ψ ρ hρ => ?_⟩
  subst hρ
  obtain ⟨-, hvanB, hisoB⟩ := hN d hd
  have hM := affineLocallyFiniteType_pullback
    (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
    (twistingTensor_affineLocallyFiniteType A ι d F hF)
  have hflatB := relativeFlat_pullback_twist_of_relativeFlat_map σ F hF d hflat
  refine ⟨fun q hq => ?_, ?_⟩
  · have h := subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding
      (i := (baseChangeIso σ ι).inv) e (baseChangeIso_inv_toSpec σ ι) hM hflatB hvanB q hq ψ
    exact (baseChangeTransCohomologyHom_bijective (toSpec A ι) σ ψ _ q).1.subsingleton
  · exact moduleCohomologyBaseChangeMap_isIso_comp (toSpec A ι) σ ψ _ 0 hisoB
      (moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
        (i := (baseChangeIso σ ι).inv) e (baseChangeIso_inv_toSpec σ ι) hM hflatB hvanB 0 ψ)

/-- **The local step of the Noetherian induction for (B) and (C)**: every irreducible closed
`Z ⊆ Spec A` meets a basic open `D(g)` on which, beyond one bound, the positive cohomology of
the fibres of `F(d)` vanishes and the fibre base-change maps in degree zero are isomorphisms. -/
theorem exists_basicOpen_twist_fiber_baseChange (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    (Z : Set (PrimeSpectrum A)) (hZc : IsClosed Z) (hZirr : IsIrreducible Z) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ (U ∩ Z).Nonempty ∧ ∃ N : ℕ, ∀ s ∈ U ∩ Z,
      ∀ d : ℤ, (N : ℤ) ≤ d →
        (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
          (moduleAddSheaf (pullback (toSpec A ι)
              (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
            ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
              (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
              ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q))
        ∧ IsIso (moduleCohomologyBaseChangeMap (toSpec A ι)
          (algebraMap A s.asIdeal.ResidueField)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  have : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have hp : (PrimeSpectrum.vanishingIdeal Z).IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hZirr
  have hZ : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set A) = Z := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  have hmem (x : PrimeSpectrum A) :
      x ∈ Z ↔ (PrimeSpectrum.vanishingIdeal Z : Set A) ⊆ x.asIdeal := by
    rw [← PrimeSpectrum.mem_zeroLocus, hZ]
  have hG := affineLocallyFiniteType_pullback
    (map (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z)) ι) hF
  obtain ⟨a, ha, hflat⟩ := exists_ne_zero_relativeFlat_pullback_away _ hG
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  let σ : A →+* Localization.Away (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z) g) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z))
  have hflatσ : relativeFlat (toSpec _ ι) ((Scheme.Modules.pullback (map σ ι)).obj F) :=
    relativeFlat_of_iso _ ((Scheme.Modules.pullbackCongr (map_comp _ _ ι)).app F ≪≫
      ((Scheme.Modules.pullbackComp _ _).app F).symm) hflat
  obtain ⟨N, hN⟩ := exists_twist_fiber_baseChange_of_relativeFlat_map n e F hF σ hflatσ
  refine ⟨PrimeSpectrum.basicOpen g, (PrimeSpectrum.basicOpen g).isOpen,
    ⟨⟨PrimeSpectrum.vanishingIdeal Z, hp⟩, ?_, ?_⟩, N, ?_⟩
  · rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    exact fun hg => ha (Ideal.Quotient.eq_zero_iff_mem.mpr hg)
  · exact (hmem _).mpr Set.Subset.rfl
  · rintro s ⟨hsg, hsZ⟩ d hd
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hsg
    have hps : PrimeSpectrum.vanishingIdeal Z ≤ s.asIdeal := (hmem s).mp hsZ
    let ψ₀ : A ⧸ PrimeSpectrum.vanishingIdeal Z →+* s.asIdeal.ResidueField :=
      Ideal.Quotient.lift _ (algebraMap A s.asIdeal.ResidueField)
        fun x hx => Ideal.algebraMap_residueField_eq_zero.mpr (hps hx)
    have hu : IsUnit (ψ₀ (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z) g)) := by
      rw [Ideal.Quotient.lift_mk]
      exact isUnit_iff_ne_zero.mpr fun h0 => hsg (Ideal.algebraMap_residueField_eq_zero.mp h0)
    let ψ : Localization.Away (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z) g) →+*
        s.asIdeal.ResidueField :=
      IsLocalization.Away.lift (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z) g) hu
    have hψ : ψ.comp σ = algebraMap A s.asIdeal.ResidueField := by
      rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp, Ideal.Quotient.lift_comp_mk]
    exact hN d hd s.asIdeal.ResidueField ψ _ hψ

variable (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
  (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)

include e hF in
/-- **(B) and (C) on the fibres**: for a coherent `F` on `P^n_A`, flat or not, there is a bound
`N` such that for every `d ≥ N` and every `s ∈ Spec A`, the positive cohomology of the fibre
`F_s(d)` on `P^n_s` vanishes and the base-change map `κ(s) ⊗_A H^0(P^n_A, F(d)) ⟶ H^0(P^n_s,
F_s(d))` is an isomorphism. -/
theorem exists_twist_fiber_vanishing_and_baseChange_isIso :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d → ∀ s : PrimeSpectrum A,
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec A ι)
            (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q))
      ∧ IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A s.asIdeal.ResidueField)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  obtain ⟨N, hN⟩ := TopologicalSpace.NoetherianSpace.exists_forall_le_of_isIrreducible _
    fun Z hZc hZirr => exists_basicOpen_twist_fiber_baseChange n e F hF Z hZc hZirr
  exact ⟨N, fun d hd s => hN s d hd⟩

include e hF in
/-- **Nitsure's (B)** (arXiv:math/0504590v1, proof of Thm 4.3, p. 21, over the affine Noetherian
base `S = Spec A`): for a coherent `F` on `P^n_A`, flat or not, there is `N₁` such that for every
`m ≥ N₁` the cohomology `H^r(P^n_A, F(m))` vanishes for `r ≥ 1`, and moreover
`H^r(P^n_s, F_s(m)) = 0` for `r ≥ 1` and every `s ∈ Spec A`. -/
theorem exists_twist_vanishing_and_fiber_vanishing :
    ∃ N₁ : ℕ, ∀ d : ℤ, (N₁ : ℤ) ≤ d →
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) q)) ∧
      ∀ s : PrimeSpectrum A, ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec A ι)
            (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨N₀, hN₀⟩ := projectiveSerreVanishing A ι n e F hF
  obtain ⟨N, hN⟩ := exists_twist_fiber_vanishing_and_baseChange_isIso n e F hF
  exact ⟨N₀ + N, fun d hd => ⟨hN₀ d (by omega), fun s => (hN d (by omega) s).1⟩⟩

include e hF in
/-- **Nitsure's (C)**, with (B) (arXiv:math/0504590v1, proof of Thm 4.3, p. 21, over the affine
Noetherian base `S = Spec A`): for a coherent `F` on `P^n_A`, flat or not, there is `N` such that
for every `m ≥ N` the statements of (B) hold and, for every `s ∈ Spec A`, the base-change map
`(π_* F(m))|_s = κ(s) ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(P^n_s, F_s(m))` is an isomorphism. -/
theorem exists_twist_vanishing_and_fiber_baseChange_isIso :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) q)) ∧
      (∀ s : PrimeSpectrum A, ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec A ι)
            (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q)) ∧
      ∀ s : PrimeSpectrum A, IsIso (moduleCohomologyBaseChangeMap (toSpec A ι)
        (algebraMap A s.asIdeal.ResidueField)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨N₀, hN₀⟩ := projectiveSerreVanishing A ι n e F hF
  obtain ⟨N, hN⟩ := exists_twist_fiber_vanishing_and_baseChange_isIso n e F hF
  exact ⟨N₀ + N, fun d hd => ⟨hN₀ d (by omega), fun s => (hN d (by omega) s).1,
    fun s => (hN d (by omega) s).2⟩⟩

include e hF in
/-- **(B) and (C) on `P^n_{κ(s)}`**: with the fibres written as `P^n_{κ(s)}` and the twists
`𝒪(d) ⊗ F_s` there, through the transport `baseChangeTwistCohomologyHom` (as in
`exists_twist_baseChange_bijective_projectiveSpace`): beyond one bound, for every
`s ∈ Spec A`, `H^q(P^n_{κ(s)}, F_s(d)) = 0` for `q ≥ 1`, and
`κ(s) ⊗_A H^0(P^n_A, F(d)) ⟶ H^0(P^n_{κ(s)}, F_s(d))` is bijective. These are the fibre
hypotheses of `bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace`. -/
theorem exists_twist_fiber_vanishing_and_bijective_projectiveSpace :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d → ∀ s : PrimeSpectrum A,
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (ProjectiveSpace s.asIdeal.ResidueField ι)
          ((moduleTensorLeftFunctor (ProjectiveSpace s.asIdeal.ResidueField ι)
            (twistingSheaf s.asIdeal.ResidueField ι d)).obj
            ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F))) q))
      ∧ Function.Bijective
        (baseChangeTwistCohomologyHom (algebraMap A s.asIdeal.ResidueField) ι d F 0 ∘
          moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A s.asIdeal.ResidueField)
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  have h := exists_twist_fiber_vanishing_and_baseChange_isIso n e F hF
  rcases h with ⟨N, hN⟩
  exact ⟨N, fun d hd s => ⟨fun q hq =>
    haveI := (hN d hd s).1 q hq
    (baseChangeTwistCohomologyHom_bijective _ ι d F q).2.subsingleton,
    haveI := (hN d hd s).2
    (baseChangeTwistCohomologyHom_bijective _ ι d F 0).comp
      (ConcreteCategory.bijective_of_isIso _)⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
