/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericHigherImages

/-! # Original generic direct-image divisibility on curves

The native bounded-below transfer is applied with the actual generic Artin
source. Artinian Picard triviality, all positive higher-image scalar
isomorphisms, and higher source divisibility are discharged. The original
Ext and derived-category universes are retained independently.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w w' dS dX dA

/-- Positive invertible scalars act bijectively on original generic
multiplicative direct-image cohomology in degrees at least two. -/
theorem genericDirectImage_nsmul_bijective_of_curve
    {k : Type u} [Field k] [IsSepClosed k]
    (X : Scheme.{u}) [IsNoetherian X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective (Sheaf.H.map
      (n • 𝟙 ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))))
      (q + 1)) := by
  exact genericDirectImage_nsmul_bijective X n q hq
    (fun r hr => genericHigherImage_positive_nsmul_isIso X p hdim n hn hunit r hr)
    (fun r hr => genericArtin_power_bijective X p hdim n hn hunit r hr)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
