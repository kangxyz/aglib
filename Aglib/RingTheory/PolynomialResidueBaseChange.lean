/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialLocalResidue
public import Mathlib.FieldTheory.Separable

/-!
# Concrete scalar base change at polynomial places

If an irreducible `q` divides the coefficient extension of an irreducible `p`,
the actual polynomial localizations admit a local ring map. Its residue map
agrees with the literal map of polynomial quotients. The rational-function map
commutes with the inclusions of these local rings. In characteristic zero the
image of the source uniformizer is itself a target uniformizer.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace Polynomial.LocalResidue

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L]
variable (φ : k →+* L) (p : k[X]) (q : L[X])
variable [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ)

include hq in
/-- A place over a factor of the coefficient extension contracts to the original place. -/
theorem primeIdeal_eq_comap :
    primeIdeal p = (primeIdeal q).comap (Polynomial.mapRingHom φ) := by
  apply Ideal.IsMaximal.eq_of_le (inferInstance : (primeIdeal p).IsMaximal)
    (Ideal.IsPrime.ne_top inferInstance)
  rw [Ideal.span_singleton_le_iff_mem]
  exact Ideal.mem_span_singleton.mpr hq

/-- The actual map between the polynomial local rings. -/
def localRingMap : Ring p →+* Ring q :=
  Localization.localRingHom (primeIdeal p) (primeIdeal q) (Polynomial.mapRingHom φ)
    (primeIdeal_eq_comap φ p q hq)

instance instIsLocalHomLocalRingMap : IsLocalHom (localRingMap φ p q hq) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- The local ring map sends a polynomial to its coefficient extension. -/
@[simp]
theorem localRingMap_polynomial (a : k[X]) :
    localRingMap φ p q hq (algebraMap k[X] (Ring p) a) =
      algebraMap L[X] (Ring q) (a.map φ) :=
  Localization.localRingHom_to_map _ _ _ _ a

/-- The map of the actual residue fields induced by the local ring map. -/
def residueMap : ResidueField p →+* ResidueField q :=
  IsLocalRing.ResidueField.map (localRingMap φ p q hq)

/-- The residue map is induced by the actual local ring map. -/
@[simp]
theorem residueMap_residue (a : Ring p) :
    residueMap φ p q hq (IsLocalRing.residue (Ring p) a) =
      IsLocalRing.residue (Ring q) (localRingMap φ p q hq a) :=
  IsLocalRing.ResidueField.map_residue _ a

/-- The coefficient-extension map on the literal polynomial quotients. -/
def adjoinRootMap : AdjoinRoot p →+* AdjoinRoot q :=
  Ideal.Quotient.lift (primeIdeal p)
    ((AdjoinRoot.mk q).comp (Polynomial.mapRingHom φ)) fun a ha => by
      apply AdjoinRoot.mk_eq_zero.mpr
      exact hq.trans (Polynomial.map_dvd φ (Ideal.mem_span_singleton.mp ha))

/-- The quotient map is coefficient extension on every polynomial class. -/
@[simp]
theorem adjoinRootMap_mk (a : k[X]) :
    adjoinRootMap φ p q hq (AdjoinRoot.mk p a) = AdjoinRoot.mk q (a.map φ) :=
  rfl

/-- In particular, the old root maps to the new root. -/
@[simp]
theorem adjoinRootMap_root :
    adjoinRootMap φ p q hq (AdjoinRoot.root p) = AdjoinRoot.root q := by
  rw [← AdjoinRoot.mk_X, adjoinRootMap_mk, Polynomial.map_X, AdjoinRoot.mk_X]

/-- Constants map through the specified coefficient-field homomorphism. -/
theorem adjoinRootMap_algebraMap (a : k) :
    adjoinRootMap φ p q hq (algebraMap k (AdjoinRoot p) a) =
      algebraMap L (AdjoinRoot q) (φ a) := by
  change adjoinRootMap φ p q hq (AdjoinRoot.mk p (C a)) = AdjoinRoot.mk q (C (φ a))
  rw [adjoinRootMap_mk, Polynomial.map_C]

/-- The concrete residue-field square commutes on every residue class. -/
theorem residueEquiv_residueMap (a : ResidueField p) :
    residueEquiv q (residueMap φ p q hq a) =
      adjoinRootMap φ p q hq (residueEquiv p a) := by
  obtain ⟨b, rfl⟩ := (adjoinRootEquiv p).surjective a
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [adjoinRootEquiv_mk]
  change residueEquiv q
    (residueMap φ p q hq (IsLocalRing.residue (Ring p) (algebraMap k[X] (Ring p) a))) = _
  rw [residueMap_residue, localRingMap_polynomial, residueEquiv_residue_polynomial,
    residueEquiv_algebraMap, adjoinRootMap_mk]

/-- The rational-function coefficient extension, induced by the actual polynomial map. -/
def fractionMap : RatFunc k →+* RatFunc L :=
  RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective φ φ.injective))

/-- The rational-function map extends polynomial coefficient extension. -/
@[simp]
theorem fractionMap_polynomial (a : k[X]) :
    fractionMap φ (algebraMap k[X] (RatFunc k) a) =
      algebraMap L[X] (RatFunc L) (a.map φ) := by
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective φ φ.injective)) a 1
  simpa only [map_one, div_one, fractionMap, RatFunc.coe_mapRingHom_eq_coe_map,
    Polynomial.coe_mapRingHom] using h

/-- The actual fraction-field map commutes with the local-ring embeddings. -/
theorem fractionMap_algebraMap_localRing (a : Ring p) :
    fractionMap φ (algebraMap (Ring p) (RatFunc k) a) =
      algebraMap (Ring q) (RatFunc L) (localRingMap φ p q hq a) := by
  have h : (fractionMap φ).comp (algebraMap (Ring p) (RatFunc k)) =
      (algebraMap (Ring q) (RatFunc L)).comp (localRingMap φ p q hq) := by
    apply IsLocalization.ringHom_ext (primeIdeal p).primeCompl
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, localRingMap_polynomial,
      ← IsScalarTower.algebraMap_apply k[X] (Ring p) (RatFunc k),
      ← IsScalarTower.algebraMap_apply L[X] (Ring q) (RatFunc L), fractionMap_polynomial]
  exact RingHom.congr_fun h a

/-- Characteristic-zero irreducibles remain squarefree under every coefficient extension. -/
theorem squarefree_map [CharZero k] : Squarefree (p.map φ) :=
  ((Fact.out : Irreducible p).separable.map).squarefree

include hq in
/-- A factor of the coefficient extension occurs exactly once. -/
theorem exists_factor_not_dvd [CharZero k] :
    ∃ h : L[X], p.map φ = q * h ∧ ¬q ∣ h := by
  obtain ⟨h, hh⟩ := hq
  refine ⟨h, hh, fun hd => ?_⟩
  apply (Fact.out : Irreducible q).not_isUnit
  apply squarefree_map φ p q
  rw [hh]
  exact mul_dvd_mul_left q hd

/-- The image of the source uniformizer is a uniformizer in the target local ring. -/
theorem irreducible_localRingMap_polynomial [CharZero k] :
    Irreducible (localRingMap φ p q hq (algebraMap k[X] (Ring p) p)) := by
  obtain ⟨h, hh, hunit⟩ := exists_factor_not_dvd φ p q hq
  rw [localRingMap_polynomial, hh, map_mul]
  exact (irreducible_mul_isUnit ((isUnit_polynomial_iff q h).mpr hunit)).mpr
    (irreducible_polynomial q)

end Polynomial.LocalResidue
