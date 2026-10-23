/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Artinian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.OriginalDivisibility

/-!
# Original cohomology of the actual generic Artin locus

The degree-one source condition in derived divisibility transfer is discharged
by the native Picard theorem for the actual Artinian scheme. Higher source
divisibility and positive higher-image divisibility remain explicit inputs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w w' dS dX dA

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The finite generic locus is an actual Artinian scheme, retaining nilpotents. -/
instance genericArtinLocus_isArtinianScheme : IsArtinianScheme (genericArtinLocus X) where

/-- Original multiplicative degree-one cohomology of the entire generic locus is trivial. -/
instance genericArtinLocus_gmH1_subsingleton
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))] :
    Subsingleton (Sheaf.H.{w} (gm (genericArtinLocus X)) 1) := inferInstance

/-- Actual generic direct-image divisibility, with the degree-one source input discharged. -/
theorem genericDirectImage_nsmul_bijective
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (n q : ℕ) (hq : 1 ≤ q)
    (hh : ∀ k : ℕ, 1 ≤ k → IsIso
      (n • 𝟙 ((higherDirectImage (genericArtinMap X) k).obj (gm (genericArtinLocus X)))))
    (hs : ∀ k : ℕ, 2 ≤ k → Function.Bijective
      (Sheaf.H.map (power (genericArtinLocus X) n) k)) :
    Function.Bijective (Sheaf.H.map
      (n • 𝟙 ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))))
      (q + 1)) := by
  apply cohomology_directImage_nsmul_bijective (genericArtinMap X)
    (gm (genericArtinLocus X)) n q hh
  · by_cases h : q = 1
    · subst q
      exact ⟨fun _ _ _ => Subsingleton.elim _ _,
        fun y => ⟨0, Subsingleton.elim _ y⟩⟩
    · exact hs q (by omega)
  · exact hs (q + 1) (by omega)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
