/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CohomologyConsequences

/-!
# Multiplicative divisibility from original root-cohomology vanishing

The original Kummer long exact sequence makes the literal multiplicative power
map bijective when root cohomology in the two adjacent degrees vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w

/-- Adjacent original root-cohomology vanishing makes the original power map bijective. -/
theorem power_bijective_of_roots_subsingleton
    (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    [Subsingleton (Sheaf.H.{w} (mu X n) q)]
    [Subsingleton (Sheaf.H.{w} (mu X n) (q + 1))] :
    Function.Bijective (Sheaf.H.map (power X n) q) := by
  exact AddCommGroupExact.bijective_of_exact_subsingleton
    (Sheaf.H.map (inclusion X n) q) (Sheaf.H.map (power X n) q)
    (boundary X n hn hinv q)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' (shortExact X n hn hinv) q))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (shortExact X n hn hinv) q (q + 1) rfl))

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
