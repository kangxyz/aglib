/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.Topology.Connected.Clopen

/-!
# Generic connectedness of smooth algebras over normal domains

Smooth base change of an integrally closed inclusion lifts generic integral
elements and idempotents. Hence a connected smooth algebra stays connected over
the fraction field. Source: the generic algebra prefix of
`R5Lab.Aglib.AlgebraicGeometry.Normalization.RestrictionInjectivity` on the supplied
source packet; no normalization-coefficient construction is imported.
-/

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace Algebra.Smooth

universe u

section Algebra
variable (R K B : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [Algebra R B] [Algebra.Smooth R B]

omit [IsDomain R] in
/-- Smooth base change of the integrally closed inclusion R -> K implies that
all B-integral elements in the actual generic algebra already come from B. -/
theorem integral_generic_has_preimage (x : B ⊗[R] K) (hx : _root_.IsIntegral B x) :
    ∃ b : B, algebraMap B (B ⊗[R] K) b = x := by
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).surjective ⟨x, hx⟩
  have h : ∀ y : B ⊗[R] integralClosure R K,
      ∃ b : B, algebraMap B (B ⊗[R] K) b =
        (TensorProduct.toIntegralClosure R B K y).val := by
    intro y
    induction y with
    | add y z hy hz =>
      obtain ⟨b, hb⟩ := hy
      obtain ⟨c, hc⟩ := hz
      exact ⟨b + c, by simp [map_add, hb, hc]⟩
    | tmul b k =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral k.property
      refine ⟨r • b, ?_⟩
      simp only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val,
        Algebra.TensorProduct.algebraMap_apply, ← hr]
      change (r • b) ⊗ₜ[R] (1 : K) = b ⊗ₜ[R] algebraMap R K r
      simpa only [Algebra.smul_def, _root_.mul_one] using (TensorProduct.smul_tmul (R := R) r b (1 :
        K))
  obtain ⟨b, hb⟩ := h y
  exact ⟨b, hb.trans (congrArg Subtype.val hy)⟩

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- The inclusion of the original smooth algebra in its generic fibre is injective. -/
theorem generic_algebraMap_injective :
    Function.Injective (algebraMap B (B ⊗[R] K)) := by
  exact Algebra.TensorProduct.includeLeft_injective
    (S := R) (A := B) (IsFractionRing.injective R K)

omit [IsDomain R] in
/-- Every idempotent of the genuine generic fibre lifts to an idempotent of B. -/
theorem generic_idempotent_lifts (e : B ⊗[R] K) (he : IsIdempotentElem e) :
    ∃ b : B, IsIdempotentElem b ∧ algebraMap B (B ⊗[R] K) b = e := by
  have hint : _root_.IsIntegral B e := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, he.eq]
  obtain ⟨b, hb⟩ := integral_generic_has_preimage R K B e hint
  refine ⟨b, ?_, hb⟩
  apply generic_algebraMap_injective R K B
  simpa only [map_mul, hb] using he.eq

end Algebra

/-- The idempotent/clopen correspondence expresses connectedness without a
normal-domain component decomposition. -/
theorem idempotent_trivial_of_preconnected (B : Type u) [CommRing B]
    [PreconnectedSpace (PrimeSpectrum B)] (e : B) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases preconnectedSpace_iff_clopen.mp inferInstance _ hc with h | h
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
    apply TopologicalSpace.Opens.ext
    simpa using h
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
    apply TopologicalSpace.Opens.ext
    simpa using h

/-- A connected smooth algebra over a normal domain has preconnected generic
fibre: no new idempotent appears after extension to the fraction field. -/
theorem generic_primeSpectrum_preconnected (R K B : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    [PreconnectedSpace (PrimeSpectrum B)] :
    PreconnectedSpace (PrimeSpectrum (B ⊗[R] K)) := by
  apply preconnectedSpace_iff_clopen.mpr
  intro U hU
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hU
  obtain ⟨b, hb, rfl⟩ := generic_idempotent_lifts R K B e he
  rcases idempotent_trivial_of_preconnected B b hb with rfl | rfl
  · left
    rw [map_zero, PrimeSpectrum.basicOpen_zero]
    rfl
  · right
    rw [map_one, PrimeSpectrum.basicOpen_one]
    rfl

/-- Nonemptiness is preserved by the injective inclusion, giving connectedness
of the actual generic algebra rather than merely preconnectedness. -/
theorem generic_primeSpectrum_connected (R K B : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum (B ⊗[R] K)) := by
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have : Nontrivial (B ⊗[R] K) :=
    ⟨⟨algebraMap B (B ⊗[R] K) 0, algebraMap B (B ⊗[R] K) 1,
      fun h => zero_ne_one (generic_algebraMap_injective R K B h)⟩⟩
  let := generic_primeSpectrum_preconnected R K B
  exact { isPreconnected_univ := isPreconnected_univ
          toNonempty := inferInstance }

end Algebra.Smooth
