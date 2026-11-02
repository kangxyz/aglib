/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.H0Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.ResidueFieldConcentration

/-!
# The original rank-one cohomology locus in amplitude at most one

For a proper coherent relatively flat family over a locally Noetherian
base, retain the actual residue-field cohomology and its original scalar
action. If these groups vanish above degree one, the locus where h0=1 and
all positive cohomology vanishes is exactly {h1<1} intersect {chi=1}.
Semicontinuity and local constancy of the original Euler characteristic
make it open. The amplitude bound is an explicit genuine hypothesis.

Pullback along the resulting original open gives the existing geometric
fibre-concentration condition for the same pulled module. This statement
constructs no new cohomology or evaluation model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X S : Scheme.{u}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] (M : X.Modules)
  (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
  (hbound : ∀ (s : S) (q : ℕ), 1 < q → Subsingleton (modulePointFiberCohomology f M q s))

include hbound in
omit [IsLocallyNoetherian S] [IsProper f] in
/-- The intrinsic Euler characteristic in actual cohomological amplitude
at most one, with the original residue-field dimensions. -/
theorem modulePointFiberEulerChar_eq_h0_sub_h1 (s : S) :
    modulePointFiberEulerChar f M s =
      (modulePointFiberCohomologyDimension f M 0 s : ℤ) -
        (modulePointFiberCohomologyDimension f M 1 s : ℤ) := by
  rw [modulePointFiberEulerChar_eq_sum_range f M s 1 (fun q hq => by
    have := hbound s q hq
    exact Module.finrank_zero_of_subsingleton)]
  simp [Finset.sum_range_succ, sub_eq_add_neg]

include hM hflat hbound in
/-- Openness of the original rank-one, degree-zero concentration locus.
Proper finiteness is used before turning zero finrank into actual vanishing. -/
theorem isOpen_setOf_modulePointFiber_rankOne :
    IsOpen {s : S | modulePointFiberCohomologyDimension f M 0 s = 1 ∧
      ∀ q : ℕ, 0 < q → Subsingleton (modulePointFiberCohomology f M q s)} := by
  have heq : {s : S | modulePointFiberCohomologyDimension f M 0 s = 1 ∧
      ∀ q : ℕ, 0 < q → Subsingleton (modulePointFiberCohomology f M q s)} =
      {s : S | modulePointFiberCohomologyDimension f M 1 s < 1} ∩
        {s : S | modulePointFiberEulerChar f M s = 1} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h0, hpos⟩
      have h1 : modulePointFiberCohomologyDimension f M 1 s = 0 := by
        have := hpos 1 (by omega)
        exact Module.finrank_zero_of_subsingleton
      refine ⟨by omega, ?_⟩
      rw [modulePointFiberEulerChar_eq_h0_sub_h1 f M hbound s, h0, h1]
      norm_num
    · rintro ⟨h1lt, hχ⟩
      have h1 : modulePointFiberCohomologyDimension f M 1 s = 0 := by omega
      have h0 : modulePointFiberCohomologyDimension f M 0 s = 1 := by
        rw [modulePointFiberEulerChar_eq_h0_sub_h1 f M hbound s, h1] at hχ
        simpa using hχ
      refine ⟨h0, fun q hq => ?_⟩
      by_cases hq1 : q = 1
      · subst q
        let := modulePointFiberCohomology_finite_of_proper f M hM 1 s
        exact Module.finrank_zero_iff.mp h1
      · exact hbound s q (by omega)
  rw [heq]
  exact ((upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper
    f M hM hflat 1).isOpen_preimage 1).inter
      ((isLocallyConstant_modulePointFiberEulerChar_of_proper f M hM hflat).isClopen_fiber 1).isOpen

/-- The actual open subscheme of rank-one degree-zero cohomology. -/
def modulePointFiberRankOneOpen : S.Opens :=
  ⟨{s : S | modulePointFiberCohomologyDimension f M 0 s = 1 ∧
      ∀ q : ℕ, 0 < q → Subsingleton (modulePointFiberCohomology f M q s)},
    isOpen_setOf_modulePointFiber_rankOne f M hM hflat hbound⟩

/-- The same family pulled back to the original open has the exact
geometric concentration required by the existing evaluation construction. -/
theorem fibreCohomologyConcentrated_rankOneOpen [M.IsQuasicoherent] :
    FibreCohomologyConcentrated
      (pullback.snd f (modulePointFiberRankOneOpen f M hM hflat hbound).ι)
      ((Scheme.Modules.pullback
        (pullback.fst f (modulePointFiberRankOneOpen f M hM hflat hbound).ι)).obj M) 1 := by
  apply fibreCohomologyConcentrated_pullback_of_range_subset
    f M (modulePointFiberRankOneOpen f M hM hflat hbound).ι 1
  · intro s hs
    rw [Scheme.Opens.range_ι] at hs
    exact hs.1
  · intro s hs q hq
    rw [Scheme.Opens.range_ι] at hs
    exact hs.2 q hq

end AlgebraicGeometry.Scheme.Cohomology
