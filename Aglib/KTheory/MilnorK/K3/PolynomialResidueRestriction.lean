/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DVRRestriction
public import Aglib.KTheory.MilnorK.K3.InfinityResidue
public import Aglib.FieldTheory.RatFuncCoefficientMap

/-!
# Restriction of actual finite and infinite Milnor K₃ residues

Over a characteristic-zero coefficient field, each irreducible factor after
coefficient extension is unramified. The concrete local-ring and fraction-field
maps therefore give the residue square on the original Milnor quotients.
The infinity square follows through the finite place `X`, actual inversion,
and the actual evaluation-at-zero equivalence.
-/

@[expose] public noncomputable section

namespace MilnorK.K3

open Polynomial Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

namespace PolynomialResidue

variable (φ : k →+* L) (p : k[X]) (q : L[X])
  [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ)

/-- The actual finite residue commutes with coefficient extension at every factor. -/
theorem residueAt_restrict [CharZero k] (x : Group (RatFunc k)) :
    residueAt q (MilnorK.K3.map (fractionMap φ) x) =
      MilnorK.K2.map (adjoinRootMap φ p q hq) (residueAt p x) := by
  have hdvr := LinearMap.congr_fun
    (DVR.residue_restrict (localRingMap φ p q hq) (fractionMap φ)
      (fractionMap_algebraMap_localRing φ p q hq)
      (irreducible_polynomial p) (irreducible_localRingMap_polynomial φ p q hq)) x
  have hsquare :
      (residueEquiv q).toRingHom.comp (residueMap φ p q hq) =
        (adjoinRootMap φ p q hq).comp (residueEquiv p).toRingHom := by
    apply RingHom.ext
    intro a
    exact residueEquiv_residueMap φ p q hq a
  change MilnorK.K2.map (residueEquiv q).toRingHom
      (DVR.residue (Ring q) (RatFunc L) (MilnorK.K3.map (fractionMap φ) x)) = _
  simp only [LinearMap.comp_apply] at hdvr
  rw [← hdvr]
  change ((MilnorK.K2.map (residueEquiv q).toRingHom).comp
    (MilnorK.K2.map (residueMap φ p q hq))) (DVR.residue (Ring p) (RatFunc k) x) = _
  rw [← MilnorK.K2.map_comp, hsquare, MilnorK.K2.map_comp]
  rfl

/-- The restriction square as equality of maps of the original Milnor groups. -/
theorem residueAt_comp_restrict [CharZero k] :
    (residueAt q).comp (MilnorK.K3.map (fractionMap φ)) =
      (MilnorK.K2.map (adjoinRootMap φ p q hq)).comp (residueAt p) := by
  apply LinearMap.ext
  intro x
  exact residueAt_restrict φ p q hq x

end PolynomialResidue

namespace InfinityResidue

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance : Fact (Irreducible (X : L[X])) := ⟨irreducible_X⟩

/-- Evaluation at zero commutes with the literal coefficient-extension quotient map. -/
theorem rootXEquiv_adjoinRootMap (φ : k →+* L) (x : AdjoinRoot (X : k[X])) :
    rootXEquiv L (adjoinRootMap φ X X (by simp) x) = φ (rootXEquiv k x) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRootMap_mk, rootXEquiv_mk, rootXEquiv_mk]
  simp

/-- The actual infinity residue commutes with the specified coefficient-field map. -/
theorem residue_restrict [CharZero k] (φ : k →+* L) (x : Group (RatFunc k)) :
    residue L (MilnorK.K3.map (fractionMap φ) x) = MilnorK.K2.map φ (residue k x) := by
  have hinv :
      (MilnorK.K3.map (RatFunc.inversion L).toRingHom).comp (MilnorK.K3.map (fractionMap φ)) =
        (MilnorK.K3.map (fractionMap φ)).comp (MilnorK.K3.map (RatFunc.inversion k).toRingHom) := by
    rw [← MilnorK.K3.map_comp, ← MilnorK.K3.map_comp, fractionMap_comp_inversion]
  have hroot : (rootXEquiv L).toRingHom.comp (adjoinRootMap φ X X (by simp)) =
      φ.comp (rootXEquiv k).toRingHom := by
    apply RingHom.ext
    intro a
    exact rootXEquiv_adjoinRootMap φ a
  change MilnorK.K2.map (rootXEquiv L).toRingHom
    (PolynomialResidue.residueAt X
      (((MilnorK.K3.map (RatFunc.inversion L).toRingHom).comp
        (MilnorK.K3.map (fractionMap φ))) x)) = _
  rw [hinv, LinearMap.comp_apply, PolynomialResidue.residueAt_restrict φ X X (by simp)]
  change ((MilnorK.K2.map (rootXEquiv L).toRingHom).comp
    (MilnorK.K2.map (adjoinRootMap φ X X (by simp)))) _ = _
  rw [← MilnorK.K2.map_comp, hroot, MilnorK.K2.map_comp]
  rfl

/-- Naturality at infinity as equality of the original integer-linear maps. -/
theorem residue_comp_restrict [CharZero k] (φ : k →+* L) :
    (residue L).comp (MilnorK.K3.map (fractionMap φ)) = (MilnorK.K2.map φ).comp (residue k) := by
  apply LinearMap.ext
  intro x
  exact residue_restrict φ x

end InfinityResidue

end MilnorK.K3
