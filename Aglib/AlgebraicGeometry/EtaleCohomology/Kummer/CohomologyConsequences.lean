/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerQuotient
public import Aglib.Algebra.Category.Grp.ExactSequenceConsequences

/-!
# Original Kummer consequences of power-map divisibility

Only the literal power maps on original multiplicative cohomology occur in
these hypotheses. Injectivity in degree two suffices for Picard-boundary
surjectivity. Bijectivity in adjacent degrees gives vanishing of root
cohomology, without asserting multiplicative cohomology itself vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology.Picard
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Injectivity of the next original multiplicative power map makes the boundary surjective. -/
theorem boundary_surjective_of_power_injective (q : ℕ)
    (hp : Function.Injective (Sheaf.H.map (power X n) (q + 1))) :
    Function.Surjective (boundary X n hn hinv q) := by
  exact AddCommGroupExact.surjective_of_exact_of_injective (boundary X n hn hinv q)
    (Sheaf.H.map (inclusion X n) (q + 1)) (Sheaf.H.map (power X n) (q + 1))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₁' (shortExact X n hn hinv) q (q + 1) rfl))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' (shortExact X n hn hinv) (q + 1))) hp

include hn hinv in
/-- Adjacent power surjectivity/injectivity kills original root cohomology. -/
theorem roots_subsingleton_of_power_surjective_injective (q : ℕ)
    (hp : Function.Surjective (Sheaf.H.map (power X n) q))
    (hq : Function.Injective (Sheaf.H.map (power X n) (q + 1))) :
    Subsingleton (Sheaf.H.{w} (mu X n) (q + 1)) := by
  exact AddCommGroupExact.subsingleton_of_exact_of_surjective (Sheaf.H.map (power X n) q)
    (boundary X n hn hinv q)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (shortExact X n hn hinv) q (q + 1) rfl)) hp
    (boundary_surjective_of_power_injective X n hn hinv q hq)

/-- The original ordinary Picard boundary is surjective if the H2 power map is injective. -/
theorem picardBoundary_surjective_of_power_injective
    (hp : Function.Injective (Sheaf.H.map (power X n) 2)) :
    Function.Surjective (picardBoundary X n hn hinv) :=
  (boundary_surjective_of_power_injective X n hn hinv 1 hp).comp
    (picardCohomologyEquiv X).surjective

/-- Under that injectivity hypothesis the existing Pic/n injection is bijective. -/
theorem picardQuotientBoundary_bijective_of_power_injective
    (hp : Function.Injective (Sheaf.H.map (power X n) 2)) :
    Function.Bijective (picardQuotientBoundary X n hn hinv) := by
  refine ⟨picardQuotientBoundary_injective X n hn hinv, ?_⟩
  intro a
  obtain ⟨c, hc⟩ := picardBoundary_surjective_of_power_injective X n hn hinv hp a
  exact ⟨QuotientAddGroup.mk c, hc⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
