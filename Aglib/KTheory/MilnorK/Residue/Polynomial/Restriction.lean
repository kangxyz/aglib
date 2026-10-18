/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Restriction
public import Aglib.KTheory.MilnorK.InfinityResidue
public import Aglib.FieldTheory.RatFuncCoefficientMap

/-!
# Coefficient restriction of finite and infinite residues in every degree

The actual local-ring maps identify the finite residue square at every
unramified factor of a coefficient-extended irreducible polynomial. In
characteristic zero every factor is unramified. At infinity the source
uniformizer maps literally to the target uniformizer, so that square holds
in arbitrary characteristic. All maps are the existing Milnor maps on the
original quotient groups; no norm or presentation independence is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

namespace PolynomialResidue

variable (φ : k →+* L) (p : k[X]) (q : L[X])
  [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ)

/-- An actual unramified factor gives the finite restriction square in every
degree. The unramified hypothesis is irreducibility of the mapped uniformizer. -/
theorem residueAt_restrict_of_unramified
    (hpq : Irreducible (localRingMap φ p q hq (algebraMap k[X] (Ring p) p)))
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residueAt q n (MilnorK.map (n + 1) (fractionMap φ) x) =
      MilnorK.map n (adjoinRootMap φ p q hq) (residueAt p n x) := by
  have hdvr := DVR.residue_restrict_apply (localRingMap φ p q hq) (fractionMap φ)
    (fractionMap_algebraMap_localRing φ p q hq) (irreducible_polynomial p) hpq n x
  have hsquare :
      (residueEquiv q).toRingHom.comp (residueMap φ p q hq) =
        (adjoinRootMap φ p q hq).comp (residueEquiv p).toRingHom := by
    apply RingHom.ext
    intro a
    exact residueEquiv_residueMap φ p q hq a
  rw [residueAt_eq_dvr, residueAt_eq_dvr]
  simp only [LinearMap.comp_apply]
  rw [← hdvr]
  change ((MilnorK.map n (residueEquiv q).toRingHom).comp
    (MilnorK.map n (residueMap φ p q hq))) (DVR.residue (Ring p) (RatFunc k) n x) = _
  rw [← MilnorK.map_comp, hsquare, MilnorK.map_comp]
  rfl

/-- Characteristic-zero irreducibles have unramified coefficient-extended
factors, hence the actual finite restriction square holds for every factor. -/
theorem residueAt_restrict [CharZero k] (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residueAt q n (MilnorK.map (n + 1) (fractionMap φ) x) =
      MilnorK.map n (adjoinRootMap φ p q hq) (residueAt p n x) :=
  residueAt_restrict_of_unramified φ p q hq
    (irreducible_localRingMap_polynomial φ p q hq) n x

/-- The finite coefficient-restriction square as equality of actual maps. -/
theorem residueAt_comp_restrict [CharZero k] (n : ℕ) :
    (residueAt q n).comp (MilnorK.map (n + 1) (fractionMap φ)) =
      (MilnorK.map n (adjoinRootMap φ p q hq)).comp (residueAt p n) := by
  apply LinearMap.ext
  intro x
  exact residueAt_restrict φ p q hq n x

end PolynomialResidue

namespace InfinityResidue

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance : Fact (Irreducible (X : L[X])) := ⟨irreducible_X⟩

/-- Evaluation at zero commutes with the actual coefficient quotient map. -/
theorem rootXEquiv_adjoinRootMap (φ : k →+* L) (x : AdjoinRoot (X : k[X])) :
    rootXEquiv L (adjoinRootMap φ X X (by simp) x) = φ (rootXEquiv k x) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRootMap_mk, rootXEquiv_mk, rootXEquiv_mk]
  simp

/-- Coefficient extension preserves infinity residues in every degree and
every characteristic, since it preserves the actual uniformizer at `X`. -/
theorem residue_restrict (φ : k →+* L) (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residue L n (MilnorK.map (n + 1) (fractionMap φ) x) =
      MilnorK.map n φ (residue k n x) := by
  have hinv :
      (MilnorK.map (n + 1) (RatFunc.inversion L).toRingHom).comp
          (MilnorK.map (n + 1) (fractionMap φ)) =
        (MilnorK.map (n + 1) (fractionMap φ)).comp
          (MilnorK.map (n + 1) (RatFunc.inversion k).toRingHom) := by
    rw [← MilnorK.map_comp, ← MilnorK.map_comp, fractionMap_comp_inversion]
  have hroot : (rootXEquiv L).toRingHom.comp (adjoinRootMap φ X X (by simp)) =
      φ.comp (rootXEquiv k).toRingHom := by
    apply RingHom.ext
    intro a
    exact rootXEquiv_adjoinRootMap φ a
  have hX : Irreducible (localRingMap φ X X (by simp)
      (algebraMap k[X] (Ring X) X)) := by
    simpa only [localRingMap_polynomial, Polynomial.map_X] using
      (irreducible_polynomial (X : L[X]))
  change MilnorK.map n (rootXEquiv L).toRingHom
    (PolynomialResidue.residueAt X n
      (((MilnorK.map (n + 1) (RatFunc.inversion L).toRingHom).comp
        (MilnorK.map (n + 1) (fractionMap φ))) x)) = _
  rw [hinv, LinearMap.comp_apply,
    PolynomialResidue.residueAt_restrict_of_unramified φ X X (by simp) hX]
  change ((MilnorK.map n (rootXEquiv L).toRingHom).comp
    (MilnorK.map n (adjoinRootMap φ X X (by simp)))) _ = _
  rw [← MilnorK.map_comp, hroot, MilnorK.map_comp]
  rfl

/-- The infinity coefficient-restriction square as equality of actual maps. -/
theorem residue_comp_restrict (φ : k →+* L) (n : ℕ) :
    (residue L n).comp (MilnorK.map (n + 1) (fractionMap φ)) =
      (MilnorK.map n φ).comp (residue k n) := by
  apply LinearMap.ext
  intro x
  exact residue_restrict φ n x

end InfinityResidue

end MilnorK
