/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DegreeFiltration

/-!
# A residue-field section modulo the actual lower polynomial stage

For a monic irreducible polynomial `p`, canonical representatives are given by
`AdjoinRoot.modByMonicHom`. The literal class `{p, reduced a, reduced b}` is
bilinear modulo the proved lower-degree span and kills Steinberg. It therefore
descends through the original integer tensor quotient defining Milnor K₂.

The actual polynomial residue kills this same lower span, descends to its
quotient, and is a left inverse of the constructed stage lift. This is a section
at one polynomial place modulo lower degree; no rational-function exactness,
finite-extension norm, or reciprocity is asserted.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.DegreeFiltration

open Polynomial
open PolynomialResidue

variable {k : Type*} [Field k]
variable (p : k[X]) [Fact (Irreducible p)]

/-- The canonical reduced polynomial of a nonzero residue-field element. -/
def reducedRepresentative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) : k[X] :=
  AdjoinRoot.modByMonicHom hp (a : AdjoinRoot p)

/-- The canonical polynomial represents the original residue-field element. -/
@[simp] theorem mk_reducedRepresentative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    AdjoinRoot.mk p (reducedRepresentative p hp a) = (a : AdjoinRoot p) :=
  AdjoinRoot.mk_leftInverse hp (a : AdjoinRoot p)

/-- A unit's canonical polynomial representative is nonzero. -/
theorem reducedRepresentative_ne_zero (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    reducedRepresentative p hp a ≠ 0 := by
  intro hzero
  have h := mk_reducedRepresentative p hp a
  rw [hzero, map_zero] at h
  exact a.ne_zero h.symm

/-- Canonical representatives have degree strictly below the modulus. -/
theorem reducedRepresentative_natDegree_lt (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    (reducedRepresentative p hp a).natDegree < p.natDegree := by
  have h : reducedRepresentative p hp a %ₘ p = reducedRepresentative p hp a := by
    rw [← AdjoinRoot.modByMonicHom_mk hp, mk_reducedRepresentative]
    rfl
  rw [← h]
  exact natDegree_modByMonic_lt _ hp (Fact.out : Irreducible p).ne_one

/-- Multiplying residue-field units takes the remainder of their polynomial product. -/
theorem reducedRepresentative_mul (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    reducedRepresentative p hp (a * b) =
      (reducedRepresentative p hp a * reducedRepresentative p hp b) %ₘ p := by
  rw [← AdjoinRoot.modByMonicHom_mk hp, map_mul, mk_reducedRepresentative,
    mk_reducedRepresentative]
  rfl

/-- The canonical representative, as a literal rational-function unit. -/
def reducedUnit (hp : p.Monic) (a : (AdjoinRoot p)ˣ) : (RatFunc k)ˣ :=
  polynomialUnit (reducedRepresentative p hp a) (reducedRepresentative_ne_zero p hp a)

/-- The polynomial product remainder describes the lifted unit without any choice. -/
theorem reducedUnit_mul (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    reducedUnit p hp (a * b) =
      polynomialUnit ((reducedRepresentative p hp a * reducedRepresentative p hp b) %ₘ p)
        (reduced_mul_ne_zero p hp _ _ (reducedRepresentative_ne_zero p hp a)
          (reducedRepresentative_ne_zero p hp b) (reducedRepresentative_natDegree_lt p hp a)
          (reducedRepresentative_natDegree_lt p hp b)) := by
  apply Units.ext
  simp only [reducedUnit, polynomialUnit_coe, reducedRepresentative_mul]

/-- The literal lifted symbol, taken modulo the actual lower-degree span. -/
def stageSymbol (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    Group (RatFunc k) ⧸ lower k p.natDegree :=
  (lower k p.natDegree).mkQ
    (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
      (reducedUnit p hp a) (reducedUnit p hp b))

/-- Multiplication of the first residue-field entry holds in the actual stage quotient. -/
theorem stageSymbol_mul_left (hp : p.Monic) (a a' b : (AdjoinRoot p)ˣ) :
    stageSymbol p hp (a * a') b = stageSymbol p hp a b + stageSymbol p hp a' b := by
  unfold stageSymbol
  rw [reducedUnit_mul]
  symm
  rw [← map_add]
  exact (Submodule.Quotient.eq _).mpr
    (reduced_mul_middle_mem_lower p hp _ _ _
      (reducedRepresentative_ne_zero p hp a) (reducedRepresentative_ne_zero p hp a')
      (reducedRepresentative_ne_zero p hp b) (reducedRepresentative_natDegree_lt p hp a)
      (reducedRepresentative_natDegree_lt p hp a') (reducedRepresentative_natDegree_lt p hp b))

/-- Multiplication of the second residue-field entry holds in the same quotient. -/
theorem stageSymbol_mul_right (hp : p.Monic) (a b b' : (AdjoinRoot p)ˣ) :
    stageSymbol p hp a (b * b') = stageSymbol p hp a b + stageSymbol p hp a b' := by
  unfold stageSymbol
  rw [reducedUnit_mul]
  symm
  rw [← map_add]
  exact (Submodule.Quotient.eq _).mpr
    (reduced_mul_right_mem_lower p hp _ _ _
      (reducedRepresentative_ne_zero p hp a) (reducedRepresentative_ne_zero p hp b)
      (reducedRepresentative_ne_zero p hp b') (reducedRepresentative_natDegree_lt p hp a)
      (reducedRepresentative_natDegree_lt p hp b) (reducedRepresentative_natDegree_lt p hp b'))

/-- Residue-field Steinberg vanishes before passing to the lower-stage quotient. -/
theorem stageSymbol_steinberg (hp : p.Monic) (a b : (AdjoinRoot p)ˣ)
    (hab : (a : AdjoinRoot p) + (b : AdjoinRoot p) = 1) : stageSymbol p hp a b = 0 := by
  unfold stageSymbol reducedUnit
  rw [reduced_steinberg p hp _ _ (reducedRepresentative_ne_zero p hp a)
    (reducedRepresentative_ne_zero p hp b) (reducedRepresentative_natDegree_lt p hp a)
    (reducedRepresentative_natDegree_lt p hp b)
    (by simpa only [mk_reducedRepresentative] using hab),
    map_zero]

/-- The proved symbol laws supply the original K₂ universal property's input. -/
def stageSymbolMap (hp : p.Monic) :
    MilnorK.K2.SymbolMap (K := AdjoinRoot p) (A := Group (RatFunc k) ⧸ lower k p.natDegree) where
  toFun := stageSymbol p hp
  mul_left := stageSymbol_mul_left p hp
  mul_right := stageSymbol_mul_right p hp
  steinberg := stageSymbol_steinberg p hp

/-- The actual integer-linear lift from the original residue-field Milnor K₂ quotient. -/
def stageLift (hp : p.Monic) :
    MilnorK.K2.Group (AdjoinRoot p) →ₗ[ℤ] Group (RatFunc k) ⧸ lower k p.natDegree :=
  MilnorK.K2.lift (MilnorK.K2.symbolMapBilinear (stageSymbolMap p hp)) (by
    intro a b hab
    exact stageSymbol_steinberg p hp a b hab)

/-- The stage lift has its literal canonical reduced-symbol value. -/
@[simp] theorem stageLift_symbol (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    stageLift p hp (MilnorK.K2.symbol a b) =
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (reducedUnit p hp a) (reducedUnit p hp b)) := rfl

/-- An already reduced polynomial is unchanged by canonical reduction. -/
theorem reducedRepresentative_quotientUnit (hp : p.Monic) (a : k[X])
    (ha : a ≠ 0) (hadeg : a.natDegree < p.natDegree) :
    reducedRepresentative p hp (quotientUnit p a (hp.not_dvd_of_natDegree_lt ha hadeg)) = a := by
  change AdjoinRoot.modByMonicHom hp (AdjoinRoot.mk p a) = a
  rw [AdjoinRoot.modByMonicHom_mk, modByMonic_eq_self_iff hp]
  exact degree_lt_degree hadeg

/-- On reduced polynomial entries, the stage lift is literally the expected triple symbol. -/
theorem stageLift_reduced (hp : p.Monic) (a b : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree) :
    stageLift p hp (MilnorK.K2.symbol
      (quotientUnit p a (hp.not_dvd_of_natDegree_lt ha hadeg))
      (quotientUnit p b (hp.not_dvd_of_natDegree_lt hb hbdeg))) =
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a ha) (polynomialUnit b hb)) := by
  rw [stageLift_symbol]
  have hunit (c : k[X]) (hc : c ≠ 0) (hcdeg : c.natDegree < p.natDegree) :
      reducedUnit p hp (quotientUnit p c (hp.not_dvd_of_natDegree_lt hc hcdeg)) =
        polynomialUnit c hc := by
    apply Units.ext
    simp only [reducedUnit, polynomialUnit_coe]
    rw [reducedRepresentative_quotientUnit p hp c hc hcdeg]
  rw [hunit a ha hadeg, hunit b hb hbdeg]

/-- The actual polynomial residue annihilates the entire lower-degree submodule. -/
theorem lower_le_ker_residueAt (hp : p.Monic) :
    lower k p.natDegree ≤ LinearMap.ker (residueAt p) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, c, ha, hb, hc, hadeg, hbdeg, hcdeg, rfl⟩
  exact residueAt_polynomial_units_zero p a b c ha hb hc
    (hp.not_dvd_of_natDegree_lt ha hadeg) (hp.not_dvd_of_natDegree_lt hb hbdeg)
    (hp.not_dvd_of_natDegree_lt hc hcdeg)

/-- The actual residue descends through exactly the lower stage used by `stageLift`. -/
def stageResidue (hp : p.Monic) :
    (Group (RatFunc k) ⧸ lower k p.natDegree) →ₗ[ℤ] MilnorK.K2.Group (AdjoinRoot p) :=
  (lower k p.natDegree).liftQ (residueAt p) (lower_le_ker_residueAt p hp)

/-- The descended residue agrees with the original residue on every quotient class. -/
theorem stageResidue_mkQ (hp : p.Monic) (x : Group (RatFunc k)) :
    stageResidue p hp ((lower k p.natDegree).mkQ x) = residueAt p x := rfl

/-- Reduction of the canonical polynomial unit recovers the original residue-field unit. -/
@[simp] theorem quotientUnit_reducedRepresentative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    quotientUnit p (reducedRepresentative p hp a)
      (hp.not_dvd_of_natDegree_lt (reducedRepresentative_ne_zero p hp a)
        (reducedRepresentative_natDegree_lt p hp a)) = a := by
  apply Units.ext
  exact mk_reducedRepresentative p hp a

/-- The descended actual residue is a left inverse of the constructed stage lift. -/
theorem stageResidue_comp_stageLift (hp : p.Monic) :
    (stageResidue p hp).comp (stageLift p hp) = LinearMap.id := by
  apply MilnorK.K2.linearMap_ext
  intro a b
  simp only [LinearMap.comp_apply, stageLift_symbol, stageResidue_mkQ,
    reducedUnit, residueAt_reduced p hp _ _ _ _ (reducedRepresentative_natDegree_lt p hp a)
      (reducedRepresentative_natDegree_lt p hp b), quotientUnit_reducedRepresentative,
    LinearMap.id_apply]

/-- The section identity holds on every original K₂ class, not only symbols. -/
@[simp] theorem stageResidue_stageLift (hp : p.Monic) (x : MilnorK.K2.Group (AdjoinRoot p)) :
    stageResidue p hp (stageLift p hp x) = x :=
  LinearMap.congr_fun (stageResidue_comp_stageLift p hp) x

/-- The actual lower-stage lift is injective. -/
theorem stageLift_injective (hp : p.Monic) : Function.Injective (stageLift p hp) :=
  Function.LeftInverse.injective (stageResidue_stageLift p hp)

/-- The residue on the lower-stage quotient is surjective. -/
theorem stageResidue_surjective (hp : p.Monic) : Function.Surjective (stageResidue p hp) :=
  Function.RightInverse.surjective (stageResidue_stageLift p hp)

end MilnorK.K3.DegreeFiltration
