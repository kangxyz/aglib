/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ArtinResidue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.FiniteCoproduct

/-!
# Actual generic-Artin cohomology from generic residue root-cohomology

The original generic stalks retain nilpotents. Only root cohomology is
transported to their residue fields; multiplicative divisibility follows
from the literal Kummer sequence on the whole generic Artin locus.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w w'

variable (X : Scheme.{u}) [IsNoetherian X]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
  [∀ η : genericPoints X, HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (X.residueField η.val)))]

/-- Actual generic residue root-vanishing gives root-vanishing on the unreduced generic locus. -/
theorem genericArtin_roots_subsingleton_of_residue
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    [∀ η : genericPoints X, Subsingleton
      (Sheaf.H.{w'} (mu (Spec (X.residueField η.val)) n) q)] :
    Subsingleton (Sheaf.H.{w} (mu (genericArtinLocus X) n) q) := by
  let : ∀ η : genericPoints X,
      HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (genericArtinComponent X η)) :=
    fun η => HasExt.standard _
  let : ∀ η : genericPoints X, Subsingleton
      (Sheaf.H.{u + 2} (mu (genericArtinComponent X η) n) q) := fun η => by
    let : HasExt.{w'} (AbelianSheaf.{u, u + 1}
        (Spec (.of (IsLocalRing.ResidueField (X.presheaf.stalk η.val))))) :=
      inferInstanceAs (HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (X.residueField η.val))))
    let : Subsingleton (Sheaf.H.{w'}
        (mu (Spec (.of (IsLocalRing.ResidueField (X.presheaf.stalk η.val)))) n) q) :=
      inferInstanceAs (Subsingleton (Sheaf.H.{w'} (mu (Spec (X.residueField η.val)) n) q))
    exact @Kummer.roots_subsingleton_of_residue.{u, u + 2, w'}
      (X.presheaf.stalk η.val) inferInstance (genericStalk_isArtinian X η)
      inferInstance inferInstance inferInstance n hn
      (levelInvertible (X.fromSpecStalk η.val) n hinv) q inferInstance
  let : HasExt.{w} (AbelianSheaf.{u, u + 1} (∐ (genericArtinComponent X))) :=
    inferInstanceAs (HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X)))
  exact Kummer.roots_subsingleton_of_finite_components.{u, w, u + 2}
    (genericArtinComponent X) n q

/-- Adjacent generic residue root-vanishing implies literal generic multiplicative divisibility. -/
theorem genericArtin_power_bijective_of_residue_roots_subsingleton
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    [∀ η : genericPoints X, Subsingleton
      (Sheaf.H.{w'} (mu (Spec (X.residueField η.val)) n) q)]
    [∀ η : genericPoints X, Subsingleton
      (Sheaf.H.{w'} (mu (Spec (X.residueField η.val)) n) (q + 1))] :
    Function.Bijective (Sheaf.H.map (power (genericArtinLocus X) n) q) := by
  let := genericArtin_roots_subsingleton_of_residue X n hn hinv q
  let := genericArtin_roots_subsingleton_of_residue X n hn hinv (q + 1)
  exact Kummer.power_bijective_of_roots_subsingleton (genericArtinLocus X) n hn
    (levelInvertible (genericArtinMap X) n hinv) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
