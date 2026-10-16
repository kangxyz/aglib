/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Original module cohomology on fibres over arbitrary scheme points

The native `Scheme.Hom.fiber` is the actual pullback along
`Y.fromSpecResidueField y : Spec κ(y) ⟶ Y`. Its coefficient is the ordinary
pullback of the original module sheaf. Its cohomology is the original
additive `Sheaf.H`, with the actual structural `κ(y)`-action from
`fiberToSpecResidueField` and `ΓSpecIso`.

The definitions need no quasicoherence, properness, Noetherianity, flatness
or finiteness hypothesis. Finiteness is a separate theorem; native `finrank`
keeps its usual convention for an infinite-dimensional vector space.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (q : ℕ) (y : Y)

/-- The original cohomology of the ordinary pulled coefficient on the native
point fibre, with its actual structural residue-field module action. -/
def modulePointFiberCohomology : ModuleCat.{u + 1} (Y.residueField y) := by
  let P := f.fiber y
  let N := (Scheme.Modules.pullback (f.fiberι y)).obj M
  let α := (f.fiberToSpecResidueField y).appTop.hom.comp
    (Scheme.ΓSpecIso (Y.residueField y)).inv.hom
  letI := moduleCohomologyModuleOfHom P α N q
  exact ModuleCat.of (Y.residueField y) (Sheaf.H.{u + 1} (moduleAddSheaf P N) q)

/-- The point-fibre module retains the literal original additive cohomology carrier. -/
theorem modulePointFiberCohomology_carrier :
    (modulePointFiberCohomology f M q y : Type (u + 1)) =
      Sheaf.H.{u + 1}
        (moduleAddSheaf (f.fiber y) ((Scheme.Modules.pullback (f.fiberι y)).obj M)) q := rfl

/-- Point-fibre scalars act by the original multiplication maps on coefficients. -/
theorem modulePointFiberCohomology_smul (a : Y.residueField y)
    (x : modulePointFiberCohomology f M q y) :
    a • x = Sheaf.H.map
      (moduleScalarOfGlobal (f.fiber y) ((Scheme.Modules.pullback (f.fiberι y)).obj M)
        ((f.fiberToSpecResidueField y).appTop
          ((Scheme.ΓSpecIso (Y.residueField y)).inv a))) q x := rfl

/-- Native dimension of the original ordinary fibre cohomology at a scheme point. -/
def modulePointFiberCohomologyDimension : ℕ :=
  Module.finrank (Y.residueField y) (modulePointFiberCohomology f M q y)

/-- The intrinsic alternating sum of original point-fibre cohomology dimensions.
Native `finsum` is zero if its support is infinite; geometric applications supply
actual locally bounded fibre cohomology rather than a bound in this definition. -/
def modulePointFiberEulerChar (f : X ⟶ Y) (M : X.Modules) (y : Y) : ℤ :=
  ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (modulePointFiberCohomologyDimension f M q y : ℤ)

/-- A proved pointwise vanishing bound computes the intrinsic Euler characteristic
by the finite alternating sum in those same actual cohomological degrees. -/
theorem modulePointFiberEulerChar_eq_sum_range (f : X ⟶ Y) (M : X.Modules) (y : Y)
    (n : ℕ) (hvan : ∀ q, n < q → modulePointFiberCohomologyDimension f M q y = 0) :
    modulePointFiberEulerChar f M y = ∑ q ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ q * (modulePointFiberCohomologyDimension f M q y : ℤ) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra h
  have hqn : ¬q < n + 1 := by simpa only [Finset.mem_coe, Finset.mem_range] using h
  have hn : n < q := lt_of_lt_of_le (Nat.lt_succ_self n) (not_lt.mp hqn)
  exact hq (by simp only [hvan q hn, Nat.cast_zero, mul_zero])

end AlgebraicGeometry.Scheme.Cohomology
