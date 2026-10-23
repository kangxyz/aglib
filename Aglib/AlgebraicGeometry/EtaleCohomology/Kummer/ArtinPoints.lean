/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DiscreteDecomposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ArtinResidue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.FiniteCoproduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Mathlib.AlgebraicGeometry.Artinian

/-! # Original root cohomology on Artinian schemes from actual point residues

The original scheme is the finite coproduct of its actual local spectra.
Only the positive-invertible root coefficients pass to the residue fields;
nilpotents are retained in the local-spectrum decomposition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

variable (X : Scheme.{u}) [IsArtinianScheme X]

/-- The actual Artinian stalk rings, without passing to a reduction. -/
theorem actualStalk_isArtinian (x : X) : IsArtinianRing (X.presheaf.stalk x) := by
  let : IsOpenImmersion (X.fromSpecStalk x) := fromSpecStalk_isOpenImmersion_of_discrete X x
  let : IsLocallyArtinian (Spec (X.presheaf.stalk x)) :=
    IsLocallyArtinian.of_isImmersion (X.fromSpecStalk x)
  exact Scheme.isLocallyArtinianScheme_Spec.mp inferInstance

variable
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ x : X, HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (X.residueField x)))]

/-- Original root-cohomology vanishing at every actual residue field implies
vanishing on the whole original Artinian scheme. -/
theorem roots_subsingleton_of_artinian_residues
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    [∀ x : X, Subsingleton (Sheaf.H.{w'} (mu (Spec (X.residueField x)) n) q)] :
    Subsingleton (Sheaf.H.{w} (mu X n) q) := by
  let C (x : X) := Spec (X.presheaf.stalk x)
  let : ∀ x : X, HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (C x)) :=
    fun x => HasExt.standard _
  let : ∀ x : X, Subsingleton (Sheaf.H.{u + 2} (mu (C x) n) q) := fun x => by
    let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Spec (.of (X.presheaf.stalk x)))) :=
      inferInstanceAs (HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (C x)))
    let : HasExt.{w'} (AbelianSheaf.{u, u + 1}
        (Spec (.of (IsLocalRing.ResidueField (X.presheaf.stalk x))))) :=
      inferInstanceAs (HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (X.residueField x))))
    let : Subsingleton (Sheaf.H.{w'}
        (mu (Spec (.of (IsLocalRing.ResidueField (X.presheaf.stalk x)))) n) q) :=
      inferInstanceAs (Subsingleton (Sheaf.H.{w'} (mu (Spec (X.residueField x)) n) q))
    exact @roots_subsingleton_of_residue.{u, u + 2, w'} (X.presheaf.stalk x)
      inferInstance (actualStalk_isArtinian X x) inferInstance inferInstance inferInstance
      n hn (levelInvertible (X.fromSpecStalk x) n hinv) q inferInstance
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (∐ C)) := HasExt.standard _
  let : Subsingleton (Sheaf.H.{u + 2} (mu (∐ C) n) q) :=
    roots_subsingleton_of_finite_components C n q
  let e := stalkCoproductIso X
  exact (rootsCohomologyPullback_bijective_of_isEquivalence.{u, w, u + 2}
    e.hom n hn hinv q).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
