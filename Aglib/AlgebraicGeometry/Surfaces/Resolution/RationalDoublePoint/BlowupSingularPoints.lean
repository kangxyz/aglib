/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ClosedSingularPoints
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional.Geometry

/-!
# Finite singular branching on the original rational ordinary blowup

Completeness supplies Nagata and J-2 of the original local base. Universal
normal-modification H1 vanishing supplies normality and dimension of the
literal ordinary maximal-ideal blowup through the existing geometric
producers. Its singular set is finite and closed, and every singular
point has a two-dimensional actual stalk.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

/-- The actual ordinary blowup of a complete rational normal local surface
has finitely many eligible closed singular centres. Normality, model
dimension and J-2 are conclusions of their original suppliers, not inputs. -/
theorem finite_closed_singularSet_of_complete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hd : ringKrullDim A = 2) (hRat : NormalModificationH1Vanishing A) :
    {x : source A hd | ¬ IsRegularLocalRing ((source A hd).presheaf.stalk x)}.Finite ∧
      IsClosed {x : source A hd | ¬ IsRegularLocalRing ((source A hd).presheaf.stalk x)} ∧
      ∀ x : source A hd, ¬ IsRegularLocalRing ((source A hd).presheaf.stalk x) →
        IsClosed ({x} : Set (source A hd)) ∧
          ringKrullDim ((source A hd).presheaf.stalk x) = 2 := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hd.le
  have hN : IsNagataRing.{u, 0} A := IsNagataRing.of_complete_local_dimLE_two A
  let : CompactSpace (source A hd) :=
    QuasiCompact.compactSpace_of_compactSpace (map A hd)
  let : IsNoetherian (source A hd) := {}
  exact Scheme.finite_closed_singularSet_of_finiteType_complete_local A (map A hd) hd.le
    (ordinary_normalStalks A hd hN hRat) (ordinary_dimension_le_two A hd hN hRat)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
