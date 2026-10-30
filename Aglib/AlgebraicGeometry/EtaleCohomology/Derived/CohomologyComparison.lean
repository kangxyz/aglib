/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.CategoryTheory.Sites.SheafCohomology.Nsmul

/-!
# Original cohomology and bounded-below derived sections

The comparison composes the original Ext/right-derived equivalence with the
native single/homology comparison. The Ext and derived-category universes
remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w dX dA

variable {X : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- The original Ext cohomology identified with native derived-sections homology. -/
def cohomologyDerivedGlobalSectionsAddEquiv
    (L : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{w} L q ≃+
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
        ((derivedGlobalSections X).obj
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj L)) :=
  (cohomologyRightDerivedAddEquiv L q).trans
    (((globalSections X).rightDerivedSingleHomologyIso q).app L).addCommGroupIsoToAddEquiv

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}] in
/-- Multiplication on original cohomology is computed by the original coefficient
endomorphism, independently of the chosen Ext universe. -/
theorem cohomology_map_nsmul_id (L : AbelianSheaf.{u, u + 1} X) (q n : ℕ)
    (x : Sheaf.H.{w} L q) : Sheaf.H.map (n • 𝟙 L) q x = n • x :=
  Sheaf.H.map_nsmul_id_apply L q n x

end AlgebraicGeometry.Scheme.EtaleCohomology
