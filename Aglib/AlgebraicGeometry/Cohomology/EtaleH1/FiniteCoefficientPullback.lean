/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteLocallyConstant
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PullbackComposition

/-!
# Pullback of genuine finite coefficient sheaves

A2/A5 support, K2-018 `eq:k2018-pointed-character` and
`eq:k2018-coefficient-compatibility`, engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de` and mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

The charts are actual scheme fibre products of the original covering charts.
Joint surjectivity is proved by the scheme pullback point-lifting theorem.
Their constant-sheaf trivializations use the proved inverse-image composition
and constant transport isomorphisms. Annihilation follows from additive inverse
image, and invertibility is mapped through the actual structure-sheaf pullback
on global sections. No connectedness, GC/FF, representability or comparison
premise is added by this generic base-change construction.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (f : S ⟶ X)
variable {L : AbelianSheaf.{u, u + 1} X}

/-- Base-change the actual covering charts and their finite constant trivializations. -/
def FiniteLocalTrivialization.pullback (t : FiniteLocalTrivialization L) :
    FiniteLocalTrivialization ((inverseImage f).obj L) where
  index := t.index
  chart i := Scheme.Etale.mk (pullback.snd (t.chart i).hom f)
  covers x := by
    obtain ⟨i, y, hy⟩ := t.covers (f x)
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨i, z, hz₂⟩
  value := t.value
  finite_value := t.finite_value
  trivialization i := by
    let a := (t.chart i).hom
    let g := pullback.fst a f
    let h := pullback.snd a f
    have square : h ≫ f = g ≫ a := pullback.condition.symm
    exact ((inverseImageComp f h).app L).symm ≪≫
      eqToIso (congrArg (fun q => (inverseImage q).obj L) square) ≪≫
      (inverseImageComp a g).app L ≪≫
      (inverseImage g).mapIso (t.trivialization i) ≪≫
      (inverseImageConstantIso g).app (t.value i)

/-- Finite local constancy survives every actual scheme inverse image. -/
theorem isFiniteLocallyConstant_pullback (h : IsFiniteLocallyConstant L) :
    IsFiniteLocallyConstant ((inverseImage f).obj L) := by
  obtain ⟨t⟩ := h
  exact ⟨t.pullback f⟩

/-- Additive inverse image preserves the same annihilator. -/
theorem killedBy_pullback {n : ℕ} (h : KilledBy n L) :
    KilledBy n ((inverseImage f).obj L) := by
  have hh := congrArg (fun q : L ⟶ L => (inverseImage f).map q) h
  simpa [KilledBy] using hh

include f in
/-- The actual map on global regular functions preserves units. -/
theorem levelInvertible_pullback {n : ℕ} (h : LevelInvertible X n) :
    LevelInvertible S n := by
  simpa only [LevelInvertible, map_natCast] using h.map f.appTop.hom

/-- The full finite coefficient package pulls back with its original positive level. -/
def FiniteCoefficient.pullback (c : FiniteCoefficient L) :
    FiniteCoefficient ((inverseImage f).obj L) where
  level := c.level
  positive := c.positive
  killed := killedBy_pullback f c.killed
  invertible := levelInvertible_pullback f c.invertible
  locally_constant := isFiniteLocallyConstant_pullback f c.locally_constant
end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 822386eea52304348053fc649714e0307c2b58b5a76edd0e5e383bbc62a382ed.
Definitions, hypotheses and universes are retained modulo native names. -/
