/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ArtinNilpotent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Divisibility
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Root-cohomology and multiplicative divisibility of an actual Artin local ring

Only root coefficients are transported through the original residue pullback.
Multiplicative divisibility is then deduced from the original Kummer sequence,
not from an assertion that inverse image preserves the multiplicative sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'

variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of (IsLocalRing.ResidueField R))))]

/-- The literal root-cohomology pullback to the actual residue field is bijective. -/
theorem rootsCohomologyPullback_residue_bijective
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) (q : ℕ) :
    Function.Bijective (rootsCohomologyPullback
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) n hn hinv q) := by
  have hI : IsNilpotent (IsLocalRing.maximalIdeal R) := by
    rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal R]
    exact IsNoetherianRing.isNilpotent_nilradical R
  let : HasExt.{w'} (AbelianSheaf.{u, u + 1}
      (Spec (.of (R ⧸ IsLocalRing.maximalIdeal R)))) :=
    inferInstanceAs (HasExt.{w'} (AbelianSheaf.{u, u + 1}
      (Spec (.of (IsLocalRing.ResidueField R)))))
  exact rootsCohomologyPullback_quotient_bijective.{u, w, w'} R
    (IsLocalRing.maximalIdeal R)
    hI n hn hinv q

/-- Residue root-cohomology vanishing gives vanishing for the actual Artin ring. -/
theorem roots_subsingleton_of_residue
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) (q : ℕ)
    [Subsingleton (Sheaf.H.{w'} (mu (Spec (.of (IsLocalRing.ResidueField R))) n) q)] :
    Subsingleton (Sheaf.H.{w} (mu (Spec (.of R)) n) q) :=
  (rootsCohomologyPullback_residue_bijective R n hn hinv q).injective.subsingleton

/-- Adjacent residue root-cohomology vanishing yields original multiplicative divisibility. -/
theorem power_bijective_of_residue_roots_subsingleton
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) (q : ℕ)
    [Subsingleton (Sheaf.H.{w'} (mu (Spec (.of (IsLocalRing.ResidueField R))) n) q)]
    [Subsingleton (Sheaf.H.{w'} (mu (Spec (.of (IsLocalRing.ResidueField R))) n) (q + 1))] :
    Function.Bijective (Sheaf.H.map (power (Spec (.of R)) n) q) := by
  let := roots_subsingleton_of_residue R n hn hinv q
  let := roots_subsingleton_of_residue R n hn hinv (q + 1)
  exact power_bijective_of_roots_subsingleton (Spec (.of R)) n hn hinv q

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
