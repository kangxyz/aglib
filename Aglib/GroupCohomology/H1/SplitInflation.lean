/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.SplitExtension
public import Mathlib.Data.ZMod.Basic

/-!
# Inflation in split continuous H1 coordinates

The existing split-coordinate base and geometric groups carry the supplied
continuous action on `ZMod n`. Inflation is actual cocycle precomposition,
descended through the same coboundary quotient. Section restriction retracts
inflation, and pointed geometric restriction detects zero.

Extracted unchanged from the closed `ContinuousCohomology` section of
`R5Lab.KTheory.Curves.IntegralCharacters`, at the accepted migration and repair
basis. The arbitrary groups, level, actions,
topologies, maps, hypotheses, and source correspondence are retained.
-/

@[expose] public section

namespace GroupCohomology.PointedCohomology

open _root_.GroupCohomology

section ContinuousCohomology

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]
  {n : ℕ} [DistribMulAction G (ZMod n)] [TopologicalSpace (ZMod n)]
  [IsTopologicalAddGroup (ZMod n)] [ContinuousSMul G (ZMod n)]

/-- The continuous H¹ of the split group with its supplied cyclic coefficient. -/
abbrev CurveH1 := ContinuousH1 (G := G) (N := N) (A := ZMod
  n)

/-- Actual direct continuous base H¹, with trivial geometric group, for the
origin subtraction in `K2-018#prop:k2018-arithmetic-characters`. -/
abbrev BaseH1 := ContinuousH1 (G := G) (N := PUnit.{1}) (A
  := ZMod n)

/-- Actual continuous geometric character group in the pointed formula used
by `K2-018#prop:k2018-arithmetic-characters`. -/
abbrev GeometricCharacters := EquivariantCharacter G N
  (ZMod n)

/-- Inflation of base cocycles along the split projection, the actual
continuous-cohomology pullback used in the origin subtraction of
`K2-018#prop:k2018-arithmetic-characters`. No cohomological section identity
is included as a premise. -/
def baseCocycleInflation : ContinuousCocycle G PUnit.{1}
  (ZMod n) →+
    ContinuousCocycle G N (ZMod n) where
  toFun c := {
    toFun x := c.toFun (PUnit.unit, x.2)
    continuous_toFun := c.continuous_toFun.comp (continuous_const.prodMk continuous_snd)
    cocycle := by intro u v g h; simpa using c.cocycle PUnit.unit PUnit.unit g h }
  map_zero' := by apply ContinuousCocycle.ext; intro x; rfl
  map_add' c d := by apply ContinuousCocycle.ext; intro x; rfl

/-- Base inflation carries the actual coefficient coboundary to the same
coboundary, the cochain step behind origin subtraction in
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem baseCocycleInflation_coboundary (a : ZMod n) :
    baseCocycleInflation (G := G) (N := N)
      (coboundaryHom (G := G) (N := PUnit.{1}) a) =
        coboundaryHom (G := G) (N := N) a := by
  apply ContinuousCocycle.ext
  intro x
  rfl

/-- Actual additive base H¹ pullback used in
`K2-018#prop:k2018-arithmetic-characters`, obtained by descending inflation
through the coboundary quotient. -/
def baseInflation : BaseH1 (G := G) (n := n) →+ CurveH1 (G := G) (N := N) (n := n) :=
  continuousH1Lift
    ((continuousH1Mk (G := G) (N := N)).comp
      baseCocycleInflation) (by
      rintro c ⟨a, rfl⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, baseCocycleInflation_coboundary]
      apply (continuousH1Mk_eq_zero_iff _).mpr
      exact ⟨a, fun _ _ => rfl⟩)

/-- Representative formula for the actual H¹ pullback used in
`K2-018#prop:k2018-arithmetic-characters`. -/
@[simp] theorem baseInflation_mk (c : ContinuousCocycle G
  PUnit.{1} (ZMod n)) :
    baseInflation (G := G) (N := N) (continuousH1Mk c) =
      continuousH1Mk (baseCocycleInflation c) := rfl

/-- The actual H¹ section restriction retracts base inflation, deriving the
origin section identity used in `K2-018#prop:k2018-arithmetic-characters`. -/
theorem section_baseInflation : Function.LeftInverse
    (continuousH1SectionRestriction (G := G) (N := N) (A :=
      ZMod n))
    (baseInflation (G := G) (N := N) (n := n)) := by
  intro q
  obtain ⟨c, rfl⟩ := continuousH1Mk_surjective q
  rw [baseInflation_mk, continuousH1SectionRestriction_mk]
  congr 1

/-- Pointed geometric restriction detects zero by the already proved
`pointedH1AddEquiv`, the direct H¹ input in
`K2-018#prop:k2018-arithmetic-characters`. Detection is a conclusion here,
not an assumed comparison map's injectivity. -/
theorem pointed_geometric_detects (q : CurveH1 (G := G) (N := N) (n := n))
    (hq : continuousH1SectionRestriction q = 0)
    (hgeom : geometricH1Hom q = 0) : q = 0 := by
  have heq : (⟨q, hq⟩ : PointedH1 (G := G) (N := N) (A :=
    ZMod n)) = 0 :=
    (pointedH1AddEquiv (G := G) (N := N) (A := ZMod
      n)).injective (by
      change geometricH1Hom q = _
      simpa using hgeom)
  exact congrArg Subtype.val heq

end ContinuousCohomology

end GroupCohomology.PointedCohomology
