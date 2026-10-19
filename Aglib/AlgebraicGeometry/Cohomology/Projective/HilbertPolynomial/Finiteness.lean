/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.RationalValues
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.NatDegree
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FlatFamily
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Integral
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finitely many Hilbert polynomials occur among the fibres

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)` and `F` a coherent module on `P^n_A =
ProjectiveSpace A ι`, flat or not. Only finitely many Hilbert polynomials occur among the fibres
`F_s = π_s^* F` on `P^n_{κ(s)}`, `s ∈ Spec A` (`finite_range_projectiveHilbertPolynomial_fiber`).
This is statement (A) in the proof of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Thm 4.3, pp. 20–21, over an affine Noetherian base.

The proof is Nitsure's Noetherian induction, in the form
`TopologicalSpace.NoetherianSpace.finite_range_of_isIrreducible`. An irreducible closed
`Z ⊆ Spec A` is `V(p)` for a prime `p`. Generic flatness over the Noetherian domain `A ⧸ p`
(`exists_ne_zero_flat_stalk_of_locallyOfFiniteType`; Nitsure Thm 4.2, p. 19; Stacks Project,
Tags 051R and 052A) gives `a ≠ 0` such that the base change of `F` to `B = (A ⧸ p)_a` is
relatively flat (`exists_ne_zero_relativeFlat_pullback_away`). Over the Noetherian ring `B` its
fibre Hilbert polynomials are locally constant on the compact space `Spec B`, hence finitely many
(`finite_range_projectiveHilbertPolynomial_fiber_of_relativeFlat`), and they are those of `F`
over `V(p) ∩ D(g)`, `g` a lift of `a`, by `projectiveHilbertPolynomial_fiber_pullback_map`.
Nitsure first stratifies `S` into finitely many reduced locally closed subschemes over which `F`
is flat; the induction here uses only the integral closed subschemes `Spec (A ⧸ p)` and their
basic opens, one at a time, and only their points enter the conclusion.

The re-indexing of Nitsure's strata by polynomials (proof of Thm 4.3, p. 22) is
`injOn_eval_projectiveHilbertPolynomial_fiber`: since the fibre Hilbert polynomials have degree
`≤ n` (`natDegree_projectiveHilbertPolynomial_le`, in `NatDegree`), for every integer `N` the map
`f ↦ (f(N), …, f(N + n))` is injective on the polynomials that occur.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {ι : Type u}

/-- **Generic flatness after base change to a basic open**: for a coherent `G` on `P_B` over a
Noetherian domain `B`, with finitely many coordinates (`[Finite ι]`), some `a ≠ 0` makes the base
change of `G` to `B_a` relatively flat over `Spec B_a` (Nitsure, arXiv:math/0504590v1, Thm 4.2,
p. 19, for `S = Spec B`; Stacks Project, Tag 052A). -/
theorem exists_ne_zero_relativeFlat_pullback_away {B : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [Finite ι] (G : (ProjectiveSpace B ι).Modules)
    (hG : affineLocallyFiniteType (ProjectiveSpace B ι) G) :
    ∃ a : B, a ≠ 0 ∧ relativeFlat (toSpec (Localization.Away a) ι)
      ((Scheme.Modules.pullback (map (algebraMap B (Localization.Away a)) ι)).obj G) := by
  have : CompactSpace (ProjectiveSpace B ι) :=
    QuasiCompact.compactSpace_of_compactSpace (toSpec B ι)
  obtain ⟨a, ha, h⟩ :=
    exists_ne_zero_flat_stalk_of_locallyOfFiniteType (A := CommRingCat.of B) (toSpec B ι) G hG
  refine ⟨a, ha, ?_⟩
  have : IsOpenImmersion (map (algebraMap B (Localization.Away a)) ι) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_map (algebraMap B (Localization.Away a)) ι).flip inferInstance
  have hres : relativeFlat (map (algebraMap B (Localization.Away a)) ι ≫ toSpec B ι)
      (G.restrict (map (algebraMap B (Localization.Away a)) ι)) := by
    intro x
    have hx : (toSpec B ι) ((map (algebraMap B (Localization.Away a)) ι) x) =
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a))))
          ((toSpec (Localization.Away a) ι) x) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f => f x) (map_toSpec (algebraMap B (Localization.Away a)) ι)
    refine flat_stalk_restrict_of_flat_stalk (map (algebraMap B (Localization.Away a)) ι)
      (toSpec B ι) G x (h _ ?_)
    rw [hx]
    intro hmem
    have hmem' : algebraMap B (Localization.Away a) a ∈
        ((toSpec (Localization.Away a) ι) x).asIdeal := hmem
    exact (toSpec (Localization.Away a) ι x).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem' (IsLocalization.Away.algebraMap_isUnit a))
  rw [map_toSpec] at hres
  exact relativeFlat_of_iso (toSpec (Localization.Away a) ι)
    ((restrictFunctorIsoPullback (map (algebraMap B (Localization.Away a)) ι)).app G).symm
    (relativeFlat_of_comp_isOpenImmersion _ _ hres)

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)

include e hF in
/-- In a flat family over a Noetherian ring only finitely many fibre Hilbert polynomials occur:
they are locally constant on the compact space `Spec A`. -/
theorem finite_range_projectiveHilbertPolynomial_fiber_of_relativeFlat
    (hflat : relativeFlat (toSpec A ι) F) :
    (Set.range fun s : PrimeSpectrum A =>
      projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F)).Finite :=
  (isLocallyConstant_projectiveHilbertPolynomial_fiber n e F hF hflat).range_finite

include e hF in
/-- **Only finitely many Hilbert polynomials occur among the fibres** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, (A), pp. 20–21, over an affine Noetherian base): for a
coherent `F` on `P^n_A`, flat or not, the Hilbert polynomials of the fibres `F_s` on
`P^n_{κ(s)}`, `s ∈ Spec A`, form a finite set. -/
theorem finite_range_projectiveHilbertPolynomial_fiber :
    (Set.range fun s : PrimeSpectrum A =>
      projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj
          F)).Finite := by
  have : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  apply TopologicalSpace.NoetherianSpace.finite_range_of_isIrreducible
  intro Z hZc hZirr
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
  have hfin := finite_range_projectiveHilbertPolynomial_fiber_of_relativeFlat n e _
    (affineLocallyFiniteType_pullback _ hG) hflat
  refine ⟨PrimeSpectrum.basicOpen g, (PrimeSpectrum.basicOpen g).isOpen,
    ⟨⟨PrimeSpectrum.vanishingIdeal Z, hp⟩, ?_, ?_⟩, hfin.subset ?_⟩
  · rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    exact fun hg => ha (Ideal.Quotient.eq_zero_iff_mem.mpr hg)
  · exact (hmem _).mpr Set.Subset.rfl
  · rintro _ ⟨s, ⟨hsg, hsZ⟩, rfl⟩
    obtain ⟨s', rfl⟩ : s ∈ Set.range
        (PrimeSpectrum.comap (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z))) := by
      rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr ((hmem s).mp hsZ)
    obtain ⟨t, rfl⟩ : s' ∈ Set.range (PrimeSpectrum.comap (algebraMap _
        (Localization.Away (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z) g)))) := by
      rw [PrimeSpectrum.localization_away_comap_range _
        (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z) g), SetLike.mem_coe,
        PrimeSpectrum.mem_basicOpen]
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hsg
      exact hsg
    refine ⟨t, ?_⟩
    dsimp only
    rw [projectiveHilbertPolynomial_fiber_pullback_map ι,
      projectiveHilbertPolynomial_fiber_pullback_map ι]

include e hF in
/-- **The polynomials that occur are determined by `n + 1` consecutive values** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, p. 22): for every integer `N`,
`f ↦ (f(N), …, f(N + n))` is injective on the fibre Hilbert polynomials of a coherent `F` on
`P^n_A`. -/
theorem injOn_eval_projectiveHilbertPolynomial_fiber (N : ℤ) :
    Set.InjOn (fun f : Polynomial ℚ => fun j : Fin (n + 1) => f.eval ((N + j : ℤ) : ℚ))
      (Set.range fun s : PrimeSpectrum A =>
        projectiveHilbertPolynomial s.asIdeal.ResidueField ι
          ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  exact Polynomial.eq_of_natDegree_le_of_eval_add_eq
    (natDegree_projectiveHilbertPolynomial_le n e _ (affineLocallyFiniteType_pullback _ hF))
    (natDegree_projectiveHilbertPolynomial_le n e _ (affineLocallyFiniteType_pullback _ hF)) N
    fun j hj => congrFun h ⟨j, Nat.lt_succ_iff.mpr hj⟩

end AlgebraicGeometry.Scheme.Cohomology
