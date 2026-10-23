/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Artin.SheafEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-!
# Original root-coefficient pullback over Artin schemes

The original cohomology pullback and the canonical root-coefficient comparison
are bijective under the actual finite-etale site equivalence. This does not
assert that inverse image preserves the multiplicative sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'

variable {X S : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- An actual inverse-image equivalence makes original root-cohomology pullback bijective. -/
theorem rootsCohomologyPullback_bijective_of_isEquivalence
    (f : S ⟶ X) [(inverseImage f).IsEquivalence]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    Function.Bijective (rootsCohomologyPullback f n hn hinv q) :=
  (cohomologyMapIso_bijective (rootsPullbackIso f n hn hinv) q).comp
    (cohomologyPullback_bijective_of_isEquivalence f (mu X n) q)

/-- Original root-cohomology invariance from the actual finite-etale Artin comparison. -/
theorem rootsCohomologyPullback_bijective_of_artin_finiteEtale_equivalence
    [IsLocallyArtinian X] [QuasiSeparatedSpace X]
    [IsLocallyArtinian S] [QuasiSeparatedSpace S]
    (f : S ⟶ X) [Surjective f] [(FiniteEtale.baseChange f).IsEquivalence]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    Function.Bijective (rootsCohomologyPullback f n hn hinv q) := by
  let := Artin.inverseImage_isEquivalence f
  exact rootsCohomologyPullback_bijective_of_isEquivalence f n hn hinv q

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
