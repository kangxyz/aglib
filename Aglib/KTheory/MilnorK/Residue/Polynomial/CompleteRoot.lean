/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.LaurentSeries
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFunction

/-!
# The upper rational local ring in the complete coefficient diagram

The polynomial local ring at `X` maps into a DVR by literal polynomial
evaluation in the supplied constant-field embedding and uniformizer. The map,
localness and commuting fraction-field square are derived, not assumed. The
complete coefficient field map is constructed from the original rational root
identification and the actual Laurent coefficient map.
-/

@[expose] public noncomputable section

open scoped RatFunc

namespace Polynomial.LocalResidue

section LocalMap

variable {B S : Type*} [Field B] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  (c : B →+* S) (t : S) (ε : B ≃+* IsLocalRing.ResidueField S)
  (hres : ∀ b, IsLocalRing.residue S (c b) = ε b) (ht : Irreducible t)

local instance : Fact (Irreducible (X : B[X])) := ⟨irreducible_X⟩

include hres ht

/-- Polynomial evaluation reduces to its original constant coefficient. -/
theorem coefficientDVR_eval_residue (q : B[X]) :
    IsLocalRing.residue S (Polynomial.eval₂RingHom c t q) = ε (q.eval 0) := by
  have h : (IsLocalRing.residue S).comp (Polynomial.eval₂RingHom c t) =
      ε.toRingHom.comp (Polynomial.evalRingHom 0) := by
    apply Polynomial.ringHom_ext
    · intro b
      simpa using hres b
    · simpa using (IsLocalRing.residue_eq_zero_iff t).mpr ht.not_isUnit
  exact RingHom.congr_fun h q

/-- Allowed denominators are units because their residue is a nonzero constant. -/
theorem coefficientDVR_eval_isUnit (q : (primeIdeal (X : B[X])).primeCompl) :
    IsUnit (Polynomial.eval₂RingHom c t (q : B[X])) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [coefficientDVR_eval_residue c t ε hres ht]
  intro h
  have hq : (q : B[X]).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact ε.injective (h.trans ε.map_zero.symm)
  exact q.property (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr hq))

/-- The actual localization lift, evaluated at the constants and uniformizer. -/
def coefficientDVRLocalMap : Ring (X : B[X]) →+* S :=
  IsLocalization.lift (S := Ring (X : B[X])) (coefficientDVR_eval_isUnit c t ε hres ht)

@[simp]
theorem coefficientDVRLocalMap_polynomial (q : B[X]) :
    coefficientDVRLocalMap c t ε hres ht (algebraMap B[X] (Ring (X : B[X])) q) =
      Polynomial.eval₂RingHom c t q :=
  IsLocalization.lift_eq (coefficientDVR_eval_isUnit c t ε hres ht) q

theorem coefficientDVRLocalMap_X :
    coefficientDVRLocalMap c t ε hres ht (algebraMap B[X] (Ring (X : B[X])) X) = t := by
  rw [coefficientDVRLocalMap_polynomial]
  exact Polynomial.eval₂_X c t

instance coefficientDVRLocalMap_isLocalHom :
    IsLocalHom (coefficientDVRLocalMap c t ε hres ht) := by
  apply ((IsLocalRing.local_hom_TFAE (coefficientDVRLocalMap c t ε hres ht)).out 4 1).mp
  rw [maximalIdeal_eq_span, Ideal.span_singleton_le_iff_mem]
  change coefficientDVRLocalMap c t ε hres ht
    (algebraMap B[X] (Ring (X : B[X])) X) ∈ IsLocalRing.maximalIdeal S
  rw [coefficientDVRLocalMap_X]
  exact ht.not_isUnit

/-- The actual induced residue-field map is the specified constant-field identification. -/
theorem coefficientDVRLocalMap_residue (a : ResidueField (X : B[X])) :
    IsLocalRing.ResidueField.map (coefficientDVRLocalMap c t ε hres ht) a =
      ε (MilnorK.InfinityResidue.rootXEquiv B
        (residueEquiv (X : B[X]) a)) := by
  obtain ⟨b, rfl⟩ := (adjoinRootEquiv (X : B[X])).surjective a
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [adjoinRootEquiv_mk]
  change IsLocalRing.ResidueField.map (coefficientDVRLocalMap c t ε hres ht)
    (IsLocalRing.residue (Ring (X : B[X]))
      (algebraMap B[X] (Ring (X : B[X])) q)) = _
  rw [IsLocalRing.ResidueField.map_residue, coefficientDVRLocalMap_polynomial,
    coefficientDVR_eval_residue c t ε hres ht, residueEquiv_algebraMap,
    MilnorK.InfinityResidue.rootXEquiv_mk]

variable {D : Type*} [Field D] [Algebra S D]
  (f : RatFunc B →+* D)
  (hC : ∀ b, f (RatFunc.C b) = algebraMap S D (c b))
  (hX : f RatFunc.X = algebraMap S D t)

include hC hX

/-- The polynomial and rational evaluations commute on the actual local ring;
only the two proved formulas on constants and `X` are needed. -/
theorem coefficientDVRLocalMap_fraction (r : Ring (X : B[X])) :
    f (algebraMap (Ring (X : B[X])) (RatFunc B) r) =
      algebraMap S D (coefficientDVRLocalMap c t ε hres ht r) := by
  have hp : f.comp (algebraMap B[X] (RatFunc B)) =
      (algebraMap S D).comp (Polynomial.eval₂RingHom c t) := by
    apply Polynomial.ringHom_ext
    · intro b
      simpa using hC b
    · simpa using hX
  have h : f.comp (algebraMap (Ring (X : B[X])) (RatFunc B)) =
      (algebraMap S D).comp (coefficientDVRLocalMap c t ε hres ht) := by
    apply IsLocalization.ringHom_ext (primeIdeal (X : B[X])).primeCompl
    apply RingHom.ext
    intro q
    simp only [RingHom.comp_apply, coefficientDVRLocalMap_polynomial,
      ← IsScalarTower.algebraMap_apply B[X] (Ring (X : B[X])) (RatFunc B)]
    exact RingHom.congr_fun hp q
  exact RingHom.congr_fun h r

end LocalMap

end Polynomial.LocalResidue

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

section LocalSquare

variable {B S D : Type*} [Field B] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field D] [Algebra S D] [IsFractionRing S D]
  (c : B →+* S) (t : S) (ε : B ≃+* IsLocalRing.ResidueField S)
  (hres : ∀ b, IsLocalRing.residue S (c b) = ε b) (ht : Irreducible t)
  (f : RatFunc B →+* D)
  (hC : ∀ b, f (RatFunc.C b) = algebraMap S D (c b))
  (hX : f RatFunc.X = algebraMap S D t)

local instance : Fact (Irreducible (X : B[X])) := ⟨irreducible_X⟩

include hres ht hC hX

/-- The upper local residue square on every Milnor class. All local-ring and
fraction-field compatibility is derived from actual polynomial evaluation. -/
theorem residueAt_X_eq_coefficientDVR_residue (n : ℕ) (x : K (RatFunc B) (n + 1)) :
    map n ε.symm.toRingHom (DVR.residue S D n (map (n + 1) f x)) =
      map n (InfinityResidue.rootXEquiv B).toRingHom (residueAt (X : B[X]) n x) := by
  have hirr : Irreducible (coefficientDVRLocalMap c t ε hres ht
      (algebraMap B[X] (Ring (X : B[X])) X)) := by
    rw [coefficientDVRLocalMap_X]
    exact ht
  have hdvr := DVR.residue_restrict_apply (coefficientDVRLocalMap c t ε hres ht)
    f (coefficientDVRLocalMap_fraction c t ε hres ht f hC hX)
    (irreducible_polynomial (X : B[X])) hirr n x
  have hsquare : ε.symm.toRingHom.comp
      (IsLocalRing.ResidueField.map (coefficientDVRLocalMap c t ε hres ht)) =
        (InfinityResidue.rootXEquiv B).toRingHom.comp (residueEquiv (X : B[X])).toRingHom := by
    apply RingHom.ext
    intro a
    change ε.symm (IsLocalRing.ResidueField.map (coefficientDVRLocalMap c t ε hres ht) a) = _
    rw [coefficientDVRLocalMap_residue, ε.symm_apply_apply]
    rfl
  rw [residueAt_eq_dvr, LinearMap.comp_apply, ← hdvr]
  change ((map n ε.symm.toRingHom).comp
    (map n (IsLocalRing.ResidueField.map (coefficientDVRLocalMap c t ε hres ht)))) _ =
      ((map n (InfinityResidue.rootXEquiv B).toRingHom).comp
        (map n (residueEquiv (X : B[X])).toRingHom)) _
  rw [← map_comp, ← map_comp, hsquare]

end LocalSquare

end MilnorK.PolynomialResidue

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k] (p : MonicIrreducible k)

local instance : Fact (Irreducible (p.val.map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

local instance : Fact (Irreducible (p.val.map (algebraMap k (RatFunc k)))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

/-- The two literal coefficient extensions agree in Laurent series. -/
theorem rationalCoefficientPolynomial_map_laurent :
    (p.val.map (RatFunc.C : k →+* RatFunc k)).map
        (algebraMap (RatFunc k) (LaurentSeries k)) =
      p.val.map (algebraMap k (LaurentSeries k)) := by
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro b
  simpa only [RingHom.comp_apply, RatFunc.coePolynomial_eq_algebraMap, RatFunc.algebraMap_C,
    Polynomial.coe_C, PowerSeries.coe_C, LaurentSeries.algebraMap_apply] using
    (RatFunc.coe_coe (C b)).symm

variable [Fact (Irreducible (p.val.map (algebraMap k (LaurentSeries k))))]

/-- The actual root-field coefficient map from rational functions to Laurent series. -/
def rationalCoefficientLaurentRootMap :
    AdjoinRoot (p.val.map (RatFunc.C : k →+* RatFunc k)) →+*
      AdjoinRoot (p.val.map (algebraMap k (LaurentSeries k))) :=
  adjoinRootMap (algebraMap (RatFunc k) (LaurentSeries k))
    (p.val.map (RatFunc.C : k →+* RatFunc k)) (p.val.map (algebraMap k (LaurentSeries k)))
    (by rw [rationalCoefficientPolynomial_map_laurent])

/-- The upper rational-function field map uses the proved original root-field
identification, followed by literal Laurent coefficient extension. -/
def rationalCoefficientLaurentMap : RatFunc (AdjoinRoot p.val) →+*
    AdjoinRoot (p.val.map (algebraMap k (LaurentSeries k))) :=
  (rationalCoefficientLaurentRootMap p).comp
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom

/-- Actual constants go to their literal coefficient-root images. -/
@[simp]
theorem rationalCoefficientLaurentMap_C (b : AdjoinRoot p.val) :
    rationalCoefficientLaurentMap p (RatFunc.C b) =
      AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val b := by
  have hb := RingHom.congr_fun (rationalCoefficientAlgEquiv_symm_comp_C p) b
  simp only [RingHom.comp_apply, rationalCoefficientPolynomial] at hb
  change rationalCoefficientLaurentRootMap p
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom
      (RatFunc.C b)) = (AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val).toRingHom b
  rw [hb, ← adjoinRootMap_eq_coefficientMap (L := LaurentSeries k) p.val]
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  change AdjoinRoot.mk (p.val.map (algebraMap k (LaurentSeries k)))
    ((q.map (RatFunc.C : k →+* RatFunc k)).map
      (algebraMap (RatFunc k) (LaurentSeries k))) =
    AdjoinRoot.mk (p.val.map (algebraMap k (LaurentSeries k)))
      (q.map (algebraMap k (LaurentSeries k)))
  rw [Polynomial.map_map]
  congr 2
  apply RingHom.ext
  intro b
  simpa only [RingHom.comp_apply, RatFunc.coePolynomial_eq_algebraMap, RatFunc.algebraMap_C,
    Polynomial.coe_C, PowerSeries.coe_C, LaurentSeries.algebraMap_apply] using
    (RatFunc.coe_coe (C b)).symm

/-- The entire rational base-field square is the original coefficient extension,
not just a formula on the chosen variable. -/
theorem rationalCoefficientLaurentMap_fractionMap (x : RatFunc k) :
    rationalCoefficientLaurentMap p (fractionMap (algebraMap k (AdjoinRoot p.val)) x) =
      algebraMap (LaurentSeries k)
        (AdjoinRoot (p.val.map (algebraMap k (LaurentSeries k))))
          (algebraMap (RatFunc k) (LaurentSeries k) x) := by
  have hx : (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm
      (fractionMap (algebraMap k (AdjoinRoot p.val)) x) =
        algebraMap (RatFunc k) (AdjoinRoot (p.val.map (RatFunc.C : k →+* RatFunc k))) x := by
    apply (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).injective
    rw [AlgEquiv.apply_symm_apply, AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap]
  change rationalCoefficientLaurentRootMap p
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm
      (fractionMap (algebraMap k (AdjoinRoot p.val)) x)) = _
  rw [hx]
  exact adjoinRootMap_algebraMap _ _ _ _ _

/-- The upper rational variable maps to the literal Laurent variable in the
complete root field. No transcendence premise or chosen embedding is introduced. -/
@[simp]
theorem rationalCoefficientLaurentMap_X :
    rationalCoefficientLaurentMap p (RatFunc.X : RatFunc (AdjoinRoot p.val)) =
      algebraMap (LaurentSeries k)
        (AdjoinRoot (p.val.map (algebraMap k (LaurentSeries k))))
          (algebraMap (RatFunc k) (LaurentSeries k) RatFunc.X) := by
  have hx : (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm
      (RatFunc.X : RatFunc (AdjoinRoot p.val)) =
        algebraMap (RatFunc k) (AdjoinRoot (p.val.map (RatFunc.C : k →+* RatFunc k)))
          RatFunc.X := by
    apply (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).injective
    rw [AlgEquiv.apply_symm_apply, AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap,
      fractionMap_X]
  change rationalCoefficientLaurentRootMap p
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm RatFunc.X) = _
  rw [hx]
  exact adjoinRootMap_algebraMap _ _ _ _ _

end MilnorK.PolynomialNorm
