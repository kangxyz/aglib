/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.RegularLocus
public import Aglib.FieldTheory.SeparablyGenerated.FinitePureConstants
public import Aglib.RingTheory.GenericFreeness.Localization
public import Aglib.RingTheory.Nagata.Defs
public import Aglib.RingTheory.RegularLocalRing.FlatDescent
public import Aglib.RingTheory.RegularLocalRing.Etale
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Aglib.RingTheory.RegularLocalRing.QuotientLift
public import Aglib.RingTheory.RegularLocalRing.RegularSequence
public import Mathlib.Data.List.OfFn
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# J-0 descent and finite normal models used in the J-2 criterion

For an injective finite-type map of Noetherian domains, J-0 of the target
implies J-0 of the source. Choose a regular away localization of the target.
Generic flatness supplies a further nonzero localization that is flat over
the original source. Its image on spectra is nonempty and open, and flat
local descent makes every point of that image regular.

This is the descent step of the finite purely inseparable model criterion.
For a semilocal Nagata base of dimension at most two, the literal normalization
of every prime quotient in every finite fraction-field extension is also J-0.
The prime-quotient J-0 to J-1 implication follows by spreading both regularity
and generation of a parameter sequence. This yields J-2 from the J-0 tests
on all finite-type domain algebras. Combining these steps with finite purely
inseparable constants proves J-2 for semilocal Nagata rings of dimension at
most two, retaining all finite-type test algebras in auxiliary universe zero.
-/

@[expose] public noncomputable section

universe u v

namespace PrimeSpectrum

/-- At the actual prime above a point, regularity descends along a flat map. -/
theorem comap_mem_regularLocus_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (hf : f.Flat) (q : PrimeSpectrum S) (hq : q ∈ regularLocus S) :
    comap f q ∈ regularLocus R := by
  change IsRegularLocalRing (Localization.AtPrime (q.asIdeal.comap f))
  let g := Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl
  have hlocal : IsLocalHom g :=
    Localization.isLocalHom_localRingHom (q.asIdeal.comap f) q.asIdeal f rfl
  exact @IsRegularLocalRing.of_flat_local _ _ _ _ _ _ hq g hlocal
    (hf.localRingHom q.asIdeal (q.asIdeal.comap f) rfl)

end PrimeSpectrum

namespace IsJ0Ring

/-- A nonzero regular finitely presented flat algebra supplies a regular open subset of its base. -/
theorem of_flat_finitePresentation_regular
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Nontrivial S] [IsRegularRing S] : IsJ0Ring R := by
  let f := PrimeSpectrum.comap (algebraMap R S)
  refine ⟨inferInstance, Set.range f, ?_, ?_, ?_⟩
  · have hopen := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := R) (S := S)
    simpa only [Set.image_univ] using hopen Set.univ isOpen_univ
  · obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum S))
    exact ⟨f q, ⟨q, rfl⟩⟩
  · rintro p ⟨q, rfl⟩
    exact PrimeSpectrum.comap_mem_regularLocus_of_flat (algebraMap R S)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) q
      (inferInstanceAs (IsRegularLocalRing (Localization.AtPrime q.asIdeal)))

/-- Generic flatness and a regular target give J-0 for the original Noetherian domain. -/
theorem of_injective_finiteType_of_regular
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [Algebra R S] [Algebra.FiniteType R S] [IsRegularRing S]
    (hinj : Function.Injective (algebraMap R S)) : IsJ0Ring R := by
  obtain ⟨a, ha, hflat⟩ :=
    Module.Finite.exists_ne_zero_flat_localizedModule_away (A := R) (B := S) S
  let : Module.Flat (Localization.Away a) (LocalizedModule.Away a S) := hflat
  have haS : algebraMap R S a ≠ 0 := by
    intro he
    apply ha
    apply hinj
    simpa only [map_zero] using he
  let T := Localization.Away (algebraMap R S a)
  let : IsDomain T := Localization.Away.isDomain haS
  let : IsRegularRing T :=
    IsRegularRing.regular_localization S T (Submonoid.powers (algebraMap R S a))
  let : Module.Flat R T :=
    Module.flat_of_isLocalizedModule_of_flat_localizedModule_away a
      (Submonoid.powers (algebraMap R S a)) (Submonoid.mem_powers _)
      (Algebra.linearMap S T)
  let : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact of_flat_finitePresentation_regular R T

/-- J-0 descends along an injective finite-type map of Noetherian domains. -/
@[stacks 07PA]
theorem of_injective_finiteType
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (hS : IsJ0Ring S) : IsJ0Ring R := by
  let : IsNoetherianRing S := hS.1
  obtain ⟨g, hg, hreg⟩ := (iff_exists_regular_away S).mp hS
  let T := Localization.Away g
  let : IsDomain T := Localization.Away.isDomain hg
  let : IsRegularRing T := hreg
  have hinjT : Function.Injective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]
    exact (IsLocalization.injective T
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg)).comp hinj
  exact of_injective_finiteType_of_regular R T hinjT

end IsJ0Ring

namespace IsNagataRing

/-- The actual finite normal models of prime quotients of a semilocal Nagata
surface are J-0. The finite extension need not be purely inseparable.
The auxiliary Japanese test universe is zero. -/
theorem isJ0Ring_integralClosure_quotient
    (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (p : Ideal R) [p.IsPrime] (L : Type u) [Field L]
    [Algebra (FractionRing (R ⧸ p)) L] [Algebra (R ⧸ p) L]
    [IsScalarTower (R ⧸ p) (FractionRing (R ⧸ p)) L]
    [FiniteDimensional (FractionRing (R ⧸ p)) L] :
    IsJ0Ring (integralClosure (R ⧸ p) L) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let D := R ⧸ p
  let N := integralClosure D L
  let : Module.Finite D N := (hR.isJapaneseRing_quotient p).finite_integralClosure L
  let : IsNoetherianRing N := IsNoetherianRing.of_finite D N
  let : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension
    (FractionRing D)
  let : Finite (MaximalSpectrum D) :=
    Module.Finite.maximalSpectrum_finite_of_finite_base R D
  let : Finite (MaximalSpectrum N) :=
    Module.Finite.maximalSpectrum_finite_of_finite_base D N
  have hND : ringKrullDim N ≤ ringKrullDim D := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap D N))
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under (R := D) hPQ
  exact IsJ0Ring.of_isIntegrallyClosed_of_dimLE_two N
    (hND.trans ((ringKrullDim_quotient_le p).trans hdim))

end IsNagataRing


open Topology TopologicalSpace

namespace PrimeSpectrum

/-- On a Noetherian spectrum, a generalization-stable set is open if each of
its points has a relative basic neighbourhood in its closure. -/
theorem isOpen_of_stableUnderGeneralization_of_generic_basicOpen
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderGeneralization s)
    (h : ∀ p ∈ s, ∃ f ∉ p.asIdeal,
      zeroLocus (p.asIdeal : Set R) ∩ (basicOpen f : Set (PrimeSpectrum R)) ⊆ s) :
    IsOpen s := by
  have H : ∀ Z : Closeds (PrimeSpectrum R), IsConstructible (s ∩ (Z : Set _)) := by
    intro Z
    apply wellFounded_lt.induction Z
    intro Z ih
    by_cases hpre : IsPreirreducible (Z : Set (PrimeSpectrum R))
    · by_cases hempty : s ∩ (Z : Set (PrimeSpectrum R)) = ∅
      · rw [hempty]
        exact IsConstructible.empty
      obtain ⟨x, hxs, hxZ⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      have hirr : IsIrreducible (Z : Set (PrimeSpectrum R)) := ⟨⟨x, hxZ⟩, hpre⟩
      let p := hirr.genericPoint
      have hgen : IsGenericPoint p (Z : Set (PrimeSpectrum R)) :=
        hirr.isGenericPoint_genericPoint Z.isClosed
      have hp : p ∈ s := hs (hgen.specializes hxZ) hxs
      obtain ⟨f, hfp, hf⟩ := h p hp
      have hZ : zeroLocus (p.asIdeal : Set R) = (Z : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.closure_singleton p).symm.trans hgen
      have hsub : (Z : Set (PrimeSpectrum R)) ∩ (basicOpen f : Set _) ⊆ s := by
        rwa [hZ] at hf
      let W : Closeds (PrimeSpectrum R) :=
        ⟨(Z : Set (PrimeSpectrum R)) \ (basicOpen f : Set _),
          Z.isClosed.sdiff (basicOpen f).isOpen⟩
      have hW : W < Z := by
        refine lt_iff_le_not_ge.mpr ⟨Set.sdiff_subset, ?_⟩
        intro hle
        exact (hle hgen.mem).2 hfp
      have hrem := ih W hW
      have hzc : IsConstructible (Z : Set (PrimeSpectrum R)) :=
        ((NoetherianSpace.isCompact ((Z : Set (PrimeSpectrum R))ᶜ)).isConstructible
          Z.isClosed.isOpen_compl).of_compl
      have huc : IsConstructible ((Z : Set (PrimeSpectrum R)) ∩ (basicOpen f : Set _)) :=
        hzc.inter isConstructible_basicOpen
      have heq : s ∩ (Z : Set (PrimeSpectrum R)) =
          ((Z : Set (PrimeSpectrum R)) ∩ (basicOpen f : Set _)) ∪
            (s ∩ (W : Set (PrimeSpectrum R))) := by
        ext y
        change (y ∈ s ∧ y ∈ Z) ↔
          (y ∈ Z ∧ y ∈ basicOpen f) ∨ (y ∈ s ∧ y ∈ Z ∧ y ∉ basicOpen f)
        constructor
        · rintro ⟨hys, hyZ⟩
          by_cases hyf : y ∈ basicOpen f
          · exact Or.inl ⟨hyZ, hyf⟩
          · exact Or.inr ⟨hys, hyZ, hyf⟩
        · rintro (hy | hy)
          · exact ⟨hsub hy, hy.1⟩
          · exact ⟨hy.1, hy.2.1⟩
      rw [heq]
      exact huc.union hrem
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hpre
      obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hn₁, hn₂⟩ := hpre
      let Z₁ : Closeds (PrimeSpectrum R) := ⟨z₁, hz₁⟩
      let Z₂ : Closeds (PrimeSpectrum R) := ⟨z₂, hz₂⟩
      have h₁ := ih (Z ⊓ Z₁) (inf_lt_left.mpr hn₁)
      have h₂ := ih (Z ⊓ Z₂) (inf_lt_left.mpr hn₂)
      have heq : s ∩ (Z : Set (PrimeSpectrum R)) =
          (s ∩ ((Z ⊓ Z₁ : Closeds (PrimeSpectrum R)) : Set _)) ∪
            (s ∩ ((Z ⊓ Z₂ : Closeds (PrimeSpectrum R)) : Set _)) := by
        ext y
        change (y ∈ s ∧ y ∈ Z) ↔
          (y ∈ s ∧ y ∈ Z ∧ y ∈ z₁) ∨ (y ∈ s ∧ y ∈ Z ∧ y ∈ z₂)
        constructor
        · rintro ⟨hys, hyZ⟩
          rcases hcover hyZ with hy₁ | hy₂
          · exact Or.inl ⟨hys, hyZ, hy₁⟩
          · exact Or.inr ⟨hys, hyZ, hy₂⟩
        · rintro (hy | hy) <;> exact ⟨hy.1, hy.2.1⟩
      rw [heq]
      exact h₁.union h₂
  apply isOpen_of_stableUnderGeneralization_of_isConstructible hs
  simpa only [Closeds.coe_top, Set.inter_univ] using H ⊤

/-- The relative basic-open formulation of the regular-locus openness criterion. -/
theorem isOpen_regularLocus_of_generic_basicOpen
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ p ∈ regularLocus R, ∃ f ∉ p.asIdeal,
      zeroLocus (p.asIdeal : Set R) ∩ (basicOpen f : Set (PrimeSpectrum R)) ⊆ regularLocus R) :
    IsOpen (regularLocus R) :=
  isOpen_of_stableUnderGeneralization_of_generic_basicOpen
    (regularLocus_stableUnderGeneralization R) h

end PrimeSpectrum


open RingTheory.Sequence
open scoped Pointwise

private theorem exists_notMem_mul_mem_of_map_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (I J : Ideal R)
    (h : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ a ∉ p, ∀ x ∈ I, a * x ∈ J := by
  classical
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  have hx (x : s) : ∃ a : p.primeCompl, (a : R) * (x : R) ∈ J := by
    have hxI : (x : R) ∈ I := by
      rw [← hs]
      exact Submodule.subset_span x.property
    have hxmap := h (Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hxI)
    obtain ⟨a, ha, hax⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
        (Localization.AtPrime p) J (x : R)).mp hxmap
    exact ⟨⟨a, ha⟩, hax⟩
  choose a ha using hx
  let b : p.primeCompl := ∏ x : s, a x
  refine ⟨b, b.property, ?_⟩
  have hI : I ≤ Submodule.comap (LinearMap.mulLeft R (b : R)) J := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    change (b : R) * x ∈ J
    have hd : a ⟨x, hx⟩ ∣ b :=
      Finset.dvd_prod_of_mem a (Finset.mem_univ (⟨x, hx⟩ : s))
    obtain ⟨c, hc⟩ := hd
    rw [show (b : R) = (a ⟨x, hx⟩ : R) * c from congrArg Subtype.val hc]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using J.mul_mem_left (c : R) (ha ⟨x, hx⟩)
  exact fun x hx => hI hx

private theorem exists_map_le_atPrime_of_map_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (I J : Ideal R)
    (h : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ a ∉ p, ∀ (q : Ideal R) [q.IsPrime], a ∉ q →
      I.map (algebraMap R (Localization.AtPrime q)) ≤
        J.map (algebraMap R (Localization.AtPrime q)) := by
  obtain ⟨a, ha, hmul⟩ := exists_notMem_mul_mem_of_map_le p I J h
  refine ⟨a, ha, fun q _ haq => ?_⟩
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime q)) (hmul x hx)
  rw [map_mul] at hmem
  exact (Ideal.unit_mul_mem_iff_mem _
    (IsLocalization.map_units (Localization.AtPrime q) (⟨a, haq⟩ : q.primeCompl))).mp hmem

private theorem exists_regular_quotient_atPrime_of_regular_quotient_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (I : Ideal R) (a : R)
    (ha : IsSMulRegular
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
      (algebraMap R (Localization.AtPrime p) a)) :
    ∃ g ∉ p, ∀ (q : Ideal R) [q.IsPrime], g ∉ q →
      IsSMulRegular (Localization.AtPrime q ⧸ I.map (algebraMap R (Localization.AtPrime q)))
        (algebraMap R (Localization.AtPrime q) a) := by
  let J : Ideal R := Submodule.comap (LinearMap.mulLeft R a) I
  have hJI : J.map (algebraMap R (Localization.AtPrime p)) ≤
      I.map (algebraMap R (Localization.AtPrime p)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have hax : a * x ∈ I := hx
    have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hax
    rw [map_mul] at hmem
    exact mem_of_isSMulRegular_quotient_of_smul_mem ha hmem
  obtain ⟨g, hg, hmul⟩ := exists_notMem_mul_mem_of_map_le p J I hJI
  refine ⟨g, hg, fun q _ hgq => ?_⟩
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro z hz
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
  change algebraMap R (Localization.AtPrime q) a * IsLocalization.mk' _ x s ∈ _ at hz
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul] at hz
  obtain ⟨t, ht, htx⟩ :=
    (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) I (a * x) s).mp hz
  have htJ : t * x ∈ J := by
    change a * (t * x) ∈ I
    simpa only [mul_left_comm] using htx
  apply (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl
    (Localization.AtPrime q) I x s).mpr
  exact ⟨g * t, q.primeCompl.mul_mem hgq ht, by simpa only [mul_assoc] using hmul _ htJ⟩

private theorem ofList_map_mul_unit {R : Type u} [CommRing R]
    (a : R) (ha : IsUnit a) (rs : List R) :
    Ideal.ofList (rs.map (a * ·)) = Ideal.ofList rs := by
  induction rs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_left_unit ha]

private theorem isSMulRegular_quotient_congr {R : Type u} [CommRing R]
    {I J : Ideal R} (h : I = J) (a : R) :
    IsSMulRegular (R ⧸ I) a ↔ IsSMulRegular (R ⧸ J) a :=
  (Ideal.quotientEquivAlgOfEq R h).toLinearEquiv.isSMulRegular_congr a

private theorem weaklyRegular_map_mul_unit {R : Type u} [CommRing R]
    (a : R) (ha : IsUnit a) (rs : List R) (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular R (rs.map (a * ·)) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < rs.length := by simpa only [List.length_map] using hi
  have hreg := (IsSMulRegular.mul_iff).mpr
    ⟨ha.isSMulRegular _, h.regular_mod_prev i hi'⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hreg ⊢
  have htake : (rs.map (a * ·)).take i = (rs.take i).map (a * ·) :=
    (List.map_take (f := (a * ·)) (l := rs) (i := i)).symm
  have heq : Ideal.ofList ((rs.map (a * ·)).take i) = Ideal.ofList (rs.take i) :=
    (congrArg Ideal.ofList htake).trans (ofList_map_mul_unit a ha (rs.take i))
  have hnew := (isSMulRegular_quotient_congr heq (a * rs[i])).mpr hreg
  simpa only [List.getElem_map] using hnew

private theorem exists_regular_generators_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)] :
    ∃ rs : List R,
      IsWeaklyRegular (Localization.AtPrime p) (rs.map (algebraMap R (Localization.AtPrime p))) ∧
      (Ideal.ofList rs).map (algebraMap R (Localization.AtPrime p)) =
        p.map (algebraMap R (Localization.AtPrime p)) := by
  classical
  let S := Localization.AtPrime p
  let d := (IsLocalRing.maximalIdeal S).spanFinrank
  obtain ⟨rs, _, hreg, hgen⟩ := IsRegularLocalRing.exists_regular_sequence_maximalIdeal S d
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl
    (fun i : Fin rs.length => rs[i])
  choose t ht using hs
  let ts := List.ofFn t
  have hts : ts.map (algebraMap R S) = rs.map (algebraMap R S s * ·) := by
    calc
      ts.map (algebraMap R S) = List.ofFn (fun i => algebraMap R S (t i)) := by
        simp only [ts, List.map_ofFn, Function.comp_def]
      _ = List.ofFn (fun i : Fin rs.length => algebraMap R S s * rs[i]) := by
        apply congrArg List.ofFn
        funext i
        simpa only [Algebra.smul_def] using ht i
      _ = rs.map (algebraMap R S s * ·) := List.ofFn_getElem_eq_map _ _
  have hsunit : IsUnit (algebraMap R S s) := IsLocalization.map_units S s
  refine ⟨ts, ?_, ?_⟩
  · rw [hts]
    exact weaklyRegular_map_mul_unit _ hsunit _ hreg.toIsWeaklyRegular
  · rw [Ideal.map_ofList, hts, ofList_map_mul_unit _ hsunit,
      hgen, Localization.AtPrime.map_eq_maximalIdeal]

private theorem exists_weaklyRegular_atPrime_of_weaklyRegular_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (rs : List R)
    (h : IsWeaklyRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ a ∉ p, ∀ (q : Ideal R) [q.IsPrime], a ∉ q →
      IsWeaklyRegular (Localization.AtPrime q)
        (rs.map (algebraMap R (Localization.AtPrime q))) := by
  classical
  have hi (i : Fin rs.length) : IsSMulRegular
      (Localization.AtPrime p ⧸ (Ideal.ofList (rs.take i)).map
        (algebraMap R (Localization.AtPrime p)))
      (algebraMap R (Localization.AtPrime p) rs[i]) := by
    have hlen : (i : ℕ) < (rs.map (algebraMap R (Localization.AtPrime p))).length := by
      rw [List.length_map]
      exact i.isLt
    have hreg := h.regular_mod_prev i hlen
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hreg
    have htake := (List.map_take (f := algebraMap R (Localization.AtPrime p))
      (l := rs) (i := (i : ℕ))).symm
    have heq := (congrArg Ideal.ofList htake).trans
      (Ideal.map_ofList (algebraMap R (Localization.AtPrime p)) (rs.take (i : ℕ))).symm
    have hnew := (isSMulRegular_quotient_congr heq
      (rs.map (algebraMap R (Localization.AtPrime p)))[(i : ℕ)]).mp hreg
    simpa only [List.getElem_map, Fin.getElem_fin] using hnew
  have hex (i : Fin rs.length) :=
    exists_regular_quotient_atPrime_of_regular_quotient_atPrime p
      (Ideal.ofList (rs.take i)) rs[i] (hi i)
  choose a ha hreg using hex
  let b : p.primeCompl := ∏ i : Fin rs.length, (⟨a i, ha i⟩ : p.primeCompl)
  refine ⟨b, b.property, fun q _ hbq => ?_⟩
  refine ⟨fun i hi => ?_⟩
  have hi' : i < rs.length := by simpa only [List.length_map] using hi
  let j : Fin rs.length := ⟨i, hi'⟩
  have haj : a j ∉ q := by
    intro hmem
    have hd : (⟨a j, ha j⟩ : p.primeCompl) ∣ b :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    obtain ⟨c, hc⟩ := hd
    apply hbq
    rw [show (b : R) = a j * c from congrArg Subtype.val hc]
    exact q.mul_mem_right _ hmem
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have htake := (List.map_take (f := algebraMap R (Localization.AtPrime q))
    (l := rs) (i := i)).symm
  have heq := (congrArg Ideal.ofList htake).trans
    (Ideal.map_ofList (algebraMap R (Localization.AtPrime q)) (rs.take i)).symm
  have hcur : IsSMulRegular
      (Localization.AtPrime q ⧸ (Ideal.ofList (rs.take i)).map
        (algebraMap R (Localization.AtPrime q)))
      (algebraMap R (Localization.AtPrime q) rs[i]) := by
    simpa only [j, Fin.getElem_fin] using hreg j q haj
  have hnew := (isSMulRegular_quotient_congr heq
    (algebraMap R (Localization.AtPrime q) rs[i])).mpr hcur
  simpa only [List.getElem_map] using hnew

private theorem regularLocal_of_weaklyRegular_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) (h : IsWeaklyRegular R rs)
    [IsRegularLocalRing (R ⧸ Ideal.ofList rs)] : IsRegularLocalRing R := by
  cases rs with
  | nil =>
    exact IsRegularLocalRing.of_ringEquiv
      ((Ideal.quotEquivOfEq (Ideal.ofList_nil (R := R))).trans (RingEquiv.quotientBot R))
  | cons a rs =>
    let Q := R ⧸ Ideal.span {a}
    let f : R →+* Q := Ideal.Quotient.mk (Ideal.span {a})
    have hproper : Ideal.ofList (a :: rs) ≠ (⊤ : Ideal R) :=
      Ideal.Quotient.nontrivial_iff.mp inferInstance
    have hproperQ : Ideal.span {a} ≠ (⊤ : Ideal R) :=
      ne_top_of_le_ne_top hproper (by rw [Ideal.ofList_cons]; exact le_sup_left)
    let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproperQ
    let : IsLocalRing Q := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
    have hcons := (isWeaklyRegular_cons_iff R a rs).mp h
    have heq : a • (⊤ : Submodule R R) = Ideal.span {a} := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    let e : QuotSMulTop a R ≃ₗ[R] Q := Submodule.quotEquivOfEq _ _ heq
    have htail : IsWeaklyRegular Q (rs.map f) :=
      (isWeaklyRegular_map_algebraMap_iff Q Q rs).mpr
        ((e.isWeaklyRegular_congr rs).mp hcons.2)
    let eqQ : (Q ⧸ Ideal.ofList (rs.map f)) ≃+* R ⧸ Ideal.ofList (a :: rs) :=
      (Ideal.quotEquivOfEq (Ideal.map_ofList f rs).symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.ofList rs)).trans
          (Ideal.quotEquivOfEq (Ideal.ofList_cons a rs).symm))
    let : IsRegularLocalRing (Q ⧸ Ideal.ofList (rs.map f)) :=
      IsRegularLocalRing.of_ringEquiv eqQ.symm
    let : IsRegularLocalRing Q := regularLocal_of_weaklyRegular_quotient Q (rs.map f) htail
    exact IsRegularLocalRing.of_quotient_span_singleton R a hcons.1
termination_by rs.length
decreasing_by simp_all only [List.length_map, List.length_cons, Nat.lt_succ_self]

private theorem regular_quotient_atPrime_of_regular_away_quotient
    {R : Type u} [CommRing R]
    (p q : Ideal R) [q.IsPrime] (hpq : p ≤ q) (b : R)
    [IsRegularRing (Localization.Away (Ideal.Quotient.mk p b))] (hbq : b ∉ q) :
    IsRegularLocalRing
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
  let D := R ⧸ p
  let Q := q.map (Ideal.Quotient.mk p)
  let : Q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hQ : Q.comap (Ideal.Quotient.mk p) = q := Ideal.comap_map_mk hpq
  have hbQ : Ideal.Quotient.mk p b ∉ Q := by
    change b ∉ Q.comap (Ideal.Quotient.mk p)
    rwa [hQ]
  let : IsRegularLocalRing (Localization.AtPrime Q) :=
    IsRegularRing.regular_atPrime_of_away D (Ideal.Quotient.mk p b) Q hbQ
  let T := Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))
  have hM : Algebra.algebraMapSubmonoid D q.primeCompl = Q.primeCompl := by
    have heq := Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective Q
    change q.primeCompl.map (algebraMap R (R ⧸ p)) = Q.primeCompl
    rw [Ideal.Quotient.algebraMap_eq]
    simpa only [hQ] using heq
  let : IsLocalization.AtPrime T Q := by
    change IsLocalization Q.primeCompl T
    rw [← hM]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) T).toRingEquiv

namespace PrimeSpectrum

/-- A J-0 prime quotient supplies a regular relative basic open near its regular generic point. -/
theorem exists_generic_basicOpen_regularLocus
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : PrimeSpectrum R) (hp : p ∈ regularLocus R) (hquot : IsJ0Ring (R ⧸ p.asIdeal)) :
    ∃ f ∉ p.asIdeal, zeroLocus (p.asIdeal : Set R) ∩
      (basicOpen f : Set (PrimeSpectrum R)) ⊆ regularLocus R := by
  let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp
  obtain ⟨rs, hseq, hgen⟩ := exists_regular_generators_atPrime p.asIdeal
  obtain ⟨a, hap, ha⟩ :=
    exists_weaklyRegular_atPrime_of_weaklyRegular_atPrime p.asIdeal rs hseq
  obtain ⟨c, hcp, hc⟩ := exists_map_le_atPrime_of_map_le p.asIdeal p.asIdeal
    (Ideal.ofList rs) hgen.ge
  have hIp : Ideal.ofList rs ≤ p.asIdeal := by
    have hle := Ideal.le_comap_map (f := algebraMap R (Localization.AtPrime p.asIdeal))
      (I := Ideal.ofList rs)
    have heq : (p.asIdeal.map (algebraMap R (Localization.AtPrime p.asIdeal))).comap
        (algebraMap R (Localization.AtPrime p.asIdeal)) = p.asIdeal :=
      Ideal.under_map_of_isLocalizationAtPrime p.asIdeal le_rfl
    rw [hgen, heq] at hle
    exact hle
  obtain ⟨b', hb', hreg⟩ := (IsJ0Ring.iff_exists_regular_away (R ⧸ p.asIdeal)).mp hquot
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b'
  have hbp : b ∉ p.asIdeal := by
    intro hm
    apply hb'
    rw [← hb]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  let : IsRegularRing (Localization.Away (Ideal.Quotient.mk p.asIdeal b)) := by
    rw [hb]
    exact hreg
  refine ⟨a * (c * b), p.asIdeal.primeCompl.mul_mem hap
    (p.asIdeal.primeCompl.mul_mem hcp hbp), ?_⟩
  rintro q ⟨hpq, hq⟩
  change a * (c * b) ∉ q.asIdeal at hq
  have hparts : a ∉ q.asIdeal ∧ c ∉ q.asIdeal ∧ b ∉ q.asIdeal := by
    simpa only [q.isPrime.mul_mem_iff_mem_or_mem, not_or] using hq
  let Q := Localization.AtPrime q.asIdeal
  have hIeq : (Ideal.ofList rs).map (algebraMap R Q) = p.asIdeal.map (algebraMap R Q) :=
    le_antisymm (Ideal.map_mono hIp) (hc q.asIdeal hparts.2.1)
  have hlist : IsWeaklyRegular Q (rs.map (algebraMap R Q)) := ha q.asIdeal hparts.1
  let : IsRegularLocalRing (Q ⧸ p.asIdeal.map (algebraMap R Q)) :=
    regular_quotient_atPrime_of_regular_away_quotient p.asIdeal q.asIdeal hpq b hparts.2.2
  have heq : Ideal.ofList (rs.map (algebraMap R Q)) = p.asIdeal.map (algebraMap R Q) := by
    rw [← Ideal.map_ofList]
    exact hIeq
  let : IsRegularLocalRing (Q ⧸ Ideal.ofList (rs.map (algebraMap R Q))) := by
    rw [heq]
    infer_instance
  exact regularLocal_of_weaklyRegular_quotient Q (rs.map (algebraMap R Q)) hlist

/-- The prime-quotient J-0 criterion for openness of the actual regular locus. -/
@[stacks 07P9]
theorem isOpen_regularLocus_of_isJ0Ring_quotients
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime], IsJ0Ring (R ⧸ p)) : IsOpen (regularLocus R) := by
  apply isOpen_regularLocus_of_generic_basicOpen R
  intro p hp
  exact exists_generic_basicOpen_regularLocus p hp (h p.asIdeal)

end PrimeSpectrum

/-- J-2 follows when every finite-type domain algebra is J-0.
All finite-type test algebras are retained in the specified universe. -/
theorem isJ2Ring_of_isJ0Ring_finiteType_domains
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
      [Algebra.FiniteType R S], IsJ0Ring S) : IsJ2Ring.{u, 0} R := by
  refine ⟨inferInstance, fun S _ _ _ => ?_⟩
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply PrimeSpectrum.isOpen_regularLocus_of_isJ0Ring_quotients S
  intro q hq
  exact h (S ⧸ q)



namespace Algebra.Etale

/-- Etale algebras over regular rings are regular, with the actual local algebra maps. -/
theorem isRegularRing_of_regular
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R] [Algebra.Etale R S] : IsRegularRing S := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.comap (algebraMap R S)
  let : q.LiesOver p := ⟨rfl⟩
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower R Rp Sq := inferInstance
  let : IsLocalHom (algebraMap Rp Sq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    exact Localization.isLocalHom_localRingHom p q (algebraMap R S) Ideal.LiesOver.over
  have hflat : (algebraMap Rp Sq).Flat := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    exact (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).localRingHom
      q p Ideal.LiesOver.over
  let : Module.Flat Rp Sq := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  exact Algebra.FormallyUnramified.isRegularLocalRing_of_flat Rp Sq

end Algebra.Etale

namespace IsJ0Ring

/-- A generically smooth domain algebra over a regular ring has a regular principal open. -/
theorem of_regular_of_generic_smooth
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [IsRegularRing R] [Algebra.FiniteType R S] [Algebra.IsSmoothAt R (⊥ : Ideal S)] :
    IsJ0Ring S := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨b, hb, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := (⊥ : Ideal S))
  let := hAlg
  let := hTower
  let := hEtale
  apply (iff_exists_regular_away S).mpr
  refine ⟨b, by simpa only [Ideal.mem_bot] using hb, ?_⟩
  exact Algebra.Etale.isRegularRing_of_regular (MvPolynomial (Fin n) R) (Localization.Away b)

/-- J-0 ascends through an injective finite-type domain algebra smooth at its generic point. -/
theorem of_injective_finiteType_of_generic_smooth
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (hR : IsJ0Ring R)
    [Algebra.IsSmoothAt R (⊥ : Ideal S)] : IsJ0Ring S := by
  let : IsNoetherianRing R := hR.1
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ha, hreg⟩ := (iff_exists_regular_away R).mp hR
  let A := Localization.Away a
  let : IsRegularRing A := hreg
  let B := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
  let : IsLocalization.Away (algebraMap R S a) B := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) B)
  have haS : algebraMap R S a ≠ 0 := by
    intro he
    apply ha
    apply hinj
    simpa only [map_zero] using he
  let : IsDomain B := IsLocalization.Away.isDomain B haS
  let : Algebra A B := inferInstance
  let : IsScalarTower R A B := inferInstance
  let : Algebra.FinitePresentation S B := IsLocalization.Away.finitePresentation (algebraMap R S a)
  let : Algebra.FiniteType R B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R S) (inferInstance : Algebra.FiniteType S B)
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType R A B
  have hinjB : Function.Injective (algebraMap S B) :=
    IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors haS)
  have hzero : Ideal.comap (algebraMap S B) (⊥ : Ideal B) = (⊥ : Ideal S) :=
    (RingHom.injective_iff_ker_eq_bot (algebraMap S B)).mp hinjB
  have hsmooth : Algebra.IsSmoothAt R (⊥ : Ideal B) := by
    have heq := Algebra.smoothLocus_comap_of_isLocalization
      (R := R) (A := S) (Af := B) (algebraMap R S a)
    have hmem : (PrimeSpectrum.comap (algebraMap S B)
        ⟨⊥, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.smoothLocus R S := by
      have he : PrimeSpectrum.comap (algebraMap S B) ⟨⊥, inferInstance⟩ =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum S) := PrimeSpectrum.ext hzero
      rw [he]
      exact inferInstanceAs (Algebra.IsSmoothAt R (⊥ : Ideal S))
    change (⟨⊥, inferInstance⟩ : PrimeSpectrum B) ∈ Algebra.smoothLocus R B
    rw [← heq]
    exact hmem
  let : Algebra.IsSmoothAt R (⊥ : Ideal B) := hsmooth
  let : IsScalarTower R A (Localization.AtPrime (⊥ : Ideal B)) :=
    IsScalarTower.to₁₂₄ R A B (Localization.AtPrime (⊥ : Ideal B))
  let : Algebra.FormallyUnramified R A :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers a)
  let : Algebra.IsSmoothAt A (⊥ : Ideal B) :=
    Algebra.FormallySmooth.of_restrictScalars R A (Localization.AtPrime (⊥ : Ideal B))
  have hB : IsJ0Ring B := of_regular_of_generic_smooth A B
  exact of_injective_finiteType S B hinjB hB

end IsJ0Ring

namespace Algebra

/-- Separating generation of the actual fraction-field map gives smoothness at the generic point. -/
theorem isSmoothAt_bot_of_separablyGenerated_fractionFields
    (R S K L : Type u) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R L]
    [IsScalarTower R S L] [Algebra K L] [IsScalarTower R K L]
    [Algebra.IsSeparablyGenerated K L] : Algebra.IsSmoothAt R (⊥ : Ideal S) := by
  obtain ⟨s, hs, hsep⟩ := (inferInstance : Algebra.IsSeparablyGenerated K L)
  let : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → L))) L := by
    convert! hsep <;> simp
  let : Algebra.FormallySmooth K L :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  let : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors R)
  let : Algebra.FormallySmooth R L := Algebra.FormallySmooth.comp R K L
  have hM : (⊥ : Ideal S).primeCompl = nonZeroDivisors S := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  let : IsLocalization.AtPrime L (⊥ : Ideal S) := by
    change IsLocalization (⊥ : Ideal S).primeCompl L
    rw [hM]
    infer_instance
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv (⊥ : Ideal S).primeCompl L
      (Localization.AtPrime (⊥ : Ideal S))).restrictScalars R)

end Algebra

/-- J-0 ascends under the actual separably generated fraction-field map. -/
@[stacks 07PB]
theorem IsJ0Ring.of_injective_finiteType_of_separablyGenerated
    (R S K L : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R L]
    [IsScalarTower R S L] [Algebra K L] [IsScalarTower R K L]
    [Algebra.IsSeparablyGenerated K L]
    (hinj : Function.Injective (algebraMap R S)) (hR : IsJ0Ring R) : IsJ0Ring S := by
  let : Algebra.IsSmoothAt R (⊥ : Ideal S) :=
    Algebra.isSmoothAt_bot_of_separablyGenerated_fractionFields R S K L
  exact IsJ0Ring.of_injective_finiteType_of_generic_smooth R S hinj hR



open scoped TensorProduct

namespace J2FiniteModel

variable (R S T Ω : Type u) [CommRing R] [CommRing S] [CommRing T] [Field Ω]
  [Algebra R S] [Algebra R T] [Algebra R Ω] [Algebra S Ω] [Algebra T Ω]
  [IsScalarTower R S Ω] [IsScalarTower R T Ω]

/-- The multiplication map into the original ambient field, regarded over S. -/
private def productMap : S ⊗[R] T →ₐ[S] Ω :=
  AlgHom.liftEquiv R S T Ω (IsScalarTower.toAlgHom R T Ω)

private theorem productMap_tmul (s : S) (t : T) :
    productMap R S T Ω (s ⊗ₜ[R] t) = algebraMap S Ω s * algebraMap T Ω t := by
  change (AlgHom.liftEquiv R S T Ω (IsScalarTower.toAlgHom R T Ω))
    (s ⊗ₜ[R] t) = _
  rw [AlgHom.liftEquiv_tmul]
  simp only [IsScalarTower.toAlgHom_apply, Algebra.smul_def]

/-- The literal ring image of the two integral models. -/
private abbrev model : Subalgebra S Ω := (productMap R S T Ω).range

private theorem model_finite [Module.Finite R T] : Module.Finite S (model R S T Ω) :=
  Module.Finite.of_surjective (productMap R S T Ω).rangeRestrict.toLinearMap
    (productMap R S T Ω).rangeRestrict_surjective

/-- The original second model maps into the tensor image by 1⊗t. -/
private def rightMap : T →ₐ[R] model R S T Ω :=
  ((productMap R S T Ω).rangeRestrict.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

private abbrev rightAlgebra : Algebra T (model R S T Ω) :=
  (rightMap R S T Ω).toAlgebra

private theorem rightTower :
    letI := rightAlgebra R S T Ω
    IsScalarTower R T (model R S T Ω) := by
  let := rightAlgebra R S T Ω
  exact IsScalarTower.of_algHom (rightMap R S T Ω)

private theorem model_finiteType_right [Algebra.FiniteType R S] :
    letI := rightAlgebra R S T Ω
    Algebra.FiniteType T (model R S T Ω) := by
  let := rightAlgebra R S T Ω
  let := rightTower R S T Ω
  let μ := productMap R S T Ω
  let g : T ⊗[R] S →ₐ[T] model R S T Ω :=
    { toRingHom := μ.rangeRestrict.toRingHom.comp (Algebra.TensorProduct.comm R T S).toRingHom
      commutes' := fun t => by
        apply Subtype.ext
        change μ ((Algebra.TensorProduct.comm R T S) (t ⊗ₜ[R] (1 : S))) =
          μ ((1 : S) ⊗ₜ[R] t)
        rw [Algebra.TensorProduct.comm_tmul] }
  have hg : Function.Surjective g :=
    μ.rangeRestrict_surjective.comp (Algebra.TensorProduct.comm R T S).surjective
  exact Algebra.FiniteType.of_surjective g hg

/-- The field closure of the ring tensor image adjoins exactly the two original images. -/
private theorem fieldClosure_model :
    Subfield.closure (model R S T Ω : Set Ω) =
      Subfield.closure (Set.range (algebraMap S Ω)) ⊔
        Subfield.closure (Set.range (algebraMap T Ω)) := by
  let F := Subfield.closure (Set.range (algebraMap S Ω)) ⊔
    Subfield.closure (Set.range (algebraMap T Ω))
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro z ⟨x, rfl⟩
    induction x with
    | tmul s t =>
      have hs : algebraMap S Ω s ∈ F :=
        (show Subfield.closure (Set.range (algebraMap S Ω)) ≤ F from le_sup_left)
          (Subfield.subset_closure ⟨s, rfl⟩)
      have ht : algebraMap T Ω t ∈ F :=
        (show Subfield.closure (Set.range (algebraMap T Ω)) ≤ F from le_sup_right)
          (Subfield.subset_closure ⟨t, rfl⟩)
      change productMap R S T Ω (s ⊗ₜ[R] t) ∈ F
      rw [productMap_tmul]
      exact F.mul_mem hs ht
    | add x y hx hy =>
      change productMap R S T Ω (x + y) ∈ F
      rw [map_add]
      exact F.add_mem hx hy
  · apply sup_le
    · apply Subfield.closure_le.mpr
      rintro _ ⟨s, rfl⟩
      apply Subfield.subset_closure
      refine ⟨s ⊗ₜ[R] (1 : T), ?_⟩
      change productMap R S T Ω (s ⊗ₜ[R] (1 : T)) = algebraMap S Ω s
      rw [productMap_tmul, map_one, mul_one]
    · apply Subfield.closure_le.mpr
      rintro _ ⟨t, rfl⟩
      apply Subfield.subset_closure
      refine ⟨(1 : S) ⊗ₜ[R] t, ?_⟩
      change productMap R S T Ω ((1 : S) ⊗ₜ[R] t) = algebraMap T Ω t
      rw [productMap_tmul, map_one, one_mul]

section FractionFields

variable (K E : Type u)
  [Field K] [Algebra S K] [IsFractionRing S K] [Algebra K Ω] [IsScalarTower S K Ω]
  [Field E] [Algebra T E] [IsFractionRing T E] [Algebra E Ω] [IsScalarTower T E Ω]

private abbrev compositum : IntermediateField E Ω :=
  IntermediateField.adjoin E (Set.range (algebraMap K Ω))

private theorem fieldClosure_model_eq_compositum :
    Subfield.closure (model R S T Ω : Set Ω) = (compositum Ω K E).toSubfield := by
  have hK : (algebraMap K Ω).fieldRange =
      Subfield.closure (Set.range (algebraMap S Ω)) := by
    simpa only [RingHom.coe_range] using
      (IsFractionRing.ringHom_fieldRange_eq_of_comp_eq (A := S) (K := K)
        (f := algebraMap K Ω) (g := algebraMap S Ω)
        (IsScalarTower.algebraMap_eq S K Ω).symm)
  have hE : (algebraMap E Ω).fieldRange =
      Subfield.closure (Set.range (algebraMap T Ω)) := by
    simpa only [RingHom.coe_range] using
      (IsFractionRing.ringHom_fieldRange_eq_of_comp_eq (A := T) (K := E)
        (f := algebraMap E Ω) (g := algebraMap T Ω)
        (IsScalarTower.algebraMap_eq T E Ω).symm)
  rw [fieldClosure_model, ← hK, ← hE]
  simp only [compositum, IntermediateField.adjoin_toSubfield, Subfield.closure_union,
    ← RingHom.coe_fieldRange, Subfield.closure_eq, sup_comm]

private def modelToCompositum : model R S T Ω →+* compositum Ω K E where
  toFun x := ⟨x, by
    change (x : Ω) ∈ (compositum Ω K E).toSubfield
    rw [← fieldClosure_model_eq_compositum R S T Ω K E]
    exact Subfield.subset_closure x.property⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private abbrev compositumModelAlgebra : Algebra (model R S T Ω) (compositum Ω K E) :=
  (modelToCompositum R S T Ω K E).toAlgebra

/-- The literal compositum is the fraction field of the actual tensor-image ring. -/
private theorem model_isFractionRing :
    letI := compositumModelAlgebra R S T Ω K E
    IsFractionRing (model R S T Ω) (compositum Ω K E) := by
  let := compositumModelAlgebra R S T Ω K E
  let : FaithfulSMul (model R S T Ω) (compositum Ω K E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro x y h
      apply Subtype.ext
      have he := congrArg (fun z : compositum Ω K E => (z : Ω)) h
      exact he)
  apply IsFractionRing.of_field
  intro z
  have hz : (z : Ω) ∈ Subfield.closure (model R S T Ω : Set Ω) := by
    rw [fieldClosure_model_eq_compositum R S T Ω K E]
    exact z.property
  obtain ⟨x, hx, y, hy, hxy⟩ := Subfield.mem_closure_iff.mp hz
  have hxP : x ∈ model R S T Ω := by
    change x ∈ Subring.closure ((model R S T Ω).toSubring : Set Ω) at hx
    change x ∈ (model R S T Ω).toSubring
    simpa only [Subring.closure_eq] using hx
  have hyP : y ∈ model R S T Ω := by
    change y ∈ Subring.closure ((model R S T Ω).toSubring : Set Ω) at hy
    change y ∈ (model R S T Ω).toSubring
    simpa only [Subring.closure_eq] using hy
  refine ⟨⟨x, hxP⟩, ⟨y, hyP⟩, ?_⟩
  apply Subtype.ext
  exact hxy.symm

/-- The actual finite tensor-image model transfers J-0 through a separably generated compositum.
Neither integral model is given an artificial algebra over its fraction field. -/
theorem isJ0Ring_of_finite_model [IsNoetherianRing R] [IsDomain S] [IsDomain T]
    [Algebra.FiniteType R S] [Module.Finite R T]
    [Algebra.IsSeparablyGenerated E
      (IntermediateField.adjoin E (Set.range (algebraMap K Ω)))]
    (hT : IsJ0Ring T) : IsJ0Ring S := by
  let P := model R S T Ω
  let N := compositum Ω K E
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsNoetherianRing T := hT.1
  let : Module.Finite S P := model_finite R S T Ω
  let : Algebra T P := rightAlgebra R S T Ω
  let : IsScalarTower R T P := rightTower R S T Ω
  let : Algebra.FiniteType T P := model_finiteType_right R S T Ω
  let : Algebra P N := compositumModelAlgebra R S T Ω K E
  let : IsFractionRing P N := model_isFractionRing R S T Ω K E
  let : Algebra T N := ((algebraMap E N).comp (algebraMap T E)).toAlgebra
  let : IsScalarTower T E N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower T P N := by
    apply IsScalarTower.of_algebraMap_eq
    intro t
    apply Subtype.ext
    change algebraMap E Ω (algebraMap T E t) =
      productMap R S T Ω ((1 : S) ⊗ₜ[R] t)
    simp only [← IsScalarTower.algebraMap_apply T E Ω, productMap,
      AlgHom.liftEquiv_tmul, one_smul, IsScalarTower.toAlgHom_apply]
  have hinjTΩ : Function.Injective (algebraMap T Ω) := by
    rw [IsScalarTower.algebraMap_eq T E Ω]
    exact (algebraMap E Ω).injective.comp (IsFractionRing.injective T E)
  have hinjTP : Function.Injective (algebraMap T P) := by
    intro x y hxy
    apply hinjTΩ
    have he := congrArg (fun z : P => (z : Ω)) hxy
    change productMap R S T Ω ((1 : S) ⊗ₜ[R] x) =
      productMap R S T Ω ((1 : S) ⊗ₜ[R] y) at he
    simpa only [productMap, AlgHom.liftEquiv_tmul, one_smul,
      IsScalarTower.toAlgHom_apply] using he
  have hP : IsJ0Ring P :=
    IsJ0Ring.of_injective_finiteType_of_separablyGenerated T P E N hinjTP hT
  have hinjSΩ : Function.Injective (algebraMap S Ω) := by
    rw [IsScalarTower.algebraMap_eq S K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective S K)
  have hinjSP : Function.Injective (algebraMap S P) := by
    intro x y hxy
    apply hinjSΩ
    exact congrArg (fun z : P => (z : Ω)) hxy
  exact IsJ0Ring.of_injective_finiteType S P hinjSP hP

end FractionFields

end J2FiniteModel



/-- A semilocal Nagata ring of dimension at most two is J-2 for all finite-type tests.
The auxiliary Nagata and J-2 universes are zero. -/
theorem IsNagataRing.isJ2Ring_of_semilocal_dimLE_two
    (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2) : IsJ2Ring.{u, 0} R := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  apply isJ2Ring_of_isJ0Ring_finiteType_domains R
  intro S _ _ _ _
  let f := algebraMap R S
  let p := RingHom.ker f
  let : p.IsPrime := RingHom.ker_isPrime f
  let D := R ⧸ p
  let : Algebra D S := f.kerLift.toAlgebra
  let : IsScalarTower R D S := IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.kerLift_mk f r).symm
  let : Algebra.FiniteType D S := Algebra.FiniteType.of_restrictScalars_finiteType R D S
  let k := FractionRing D
  let K := FractionRing S
  have hinjDK : Function.Injective (algebraMap D K) := by
    rw [IsScalarTower.algebraMap_eq D S K]
    exact (IsFractionRing.injective S K).comp f.kerLift_injective
  let : FaithfulSMul D K := (faithfulSMul_iff_algebraMap_injective D K).mpr hinjDK
  let : Algebra k K := FractionRing.liftAlgebra D K
  let : IsScalarTower D k K := FractionRing.isScalarTower_liftAlgebra D K
  let : Algebra.EssFiniteType D K := Algebra.EssFiniteType.comp D S K
  let : Algebra.EssFiniteType k K := Algebra.EssFiniteType.of_comp D k K
  let Ω := AlgebraicClosure K
  let : Algebra k Ω := inferInstance
  let : IsScalarTower k K Ω := inferInstance
  let : Algebra S Ω := inferInstance
  let : IsScalarTower S K Ω := inferInstance
  let : Algebra R Ω := inferInstance
  let : IsScalarTower R S Ω := inferInstance
  let : Algebra D Ω := inferInstance
  let : IsScalarTower D k Ω := inferInstance
  let : IsScalarTower D K Ω := IsScalarTower.to₁₃₄ D k K Ω
  let : IsScalarTower D S Ω := IsScalarTower.to₁₂₄ D S K Ω
  let : IsScalarTower R D Ω := IsScalarTower.to₁₂₄ R D S Ω
  obtain ⟨E, hEfin, _, hsep⟩ := Algebra.FinitePureConstants.exists_constants k K Ω
  let : FiniteDimensional k E := hEfin
  let : Algebra D E := ((algebraMap k E).comp (algebraMap D k)).toAlgebra
  let : IsScalarTower D k E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower D E Ω := IsScalarTower.to₁₃₄ D k E Ω
  let T := integralClosure D E
  let : Module.Finite D T := (hR.isJapaneseRing_quotient p).finite_integralClosure E
  let : Algebra R T := ((algebraMap D T).comp (algebraMap R D)).toAlgebra
  let : IsScalarTower R D T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite R T := Module.Finite.trans D T
  let : IsFractionRing T E := integralClosure.isFractionRing_of_finite_extension k E
  let : Algebra T Ω := ((algebraMap E Ω).comp (algebraMap T E)).toAlgebra
  let : @IsScalarTower T E Ω
      (inferInstance : Algebra T E).toSMul
      (inferInstance : Algebra E Ω).toSMul
      (inferInstance : Algebra T Ω).toSMul :=
    IsScalarTower.of_algebraMap_eq (R := T) (S := E) (A := Ω) fun _ => rfl
  let : @IsScalarTower R T Ω
      (inferInstance : Algebra R T).toSMul
      (inferInstance : Algebra T Ω).toSMul
      (inferInstance : Algebra R Ω).toSMul :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := T) (A := Ω) fun r => by
      change algebraMap R Ω r =
        algebraMap E Ω (algebraMap T E (algebraMap D T (algebraMap R D r)))
      rw [← IsScalarTower.algebraMap_apply D T E,
        ← IsScalarTower.algebraMap_apply D E Ω,
        ← IsScalarTower.algebraMap_apply R D Ω]
  let : Algebra.IsSeparablyGenerated E
      (IntermediateField.adjoin E (Set.range (algebraMap K Ω))) := hsep
  have hT : IsJ0Ring T := IsNagataRing.isJ0Ring_integralClosure_quotient R hR hdim p E
  exact J2FiniteModel.isJ0Ring_of_finite_model R S T Ω K E hT
