/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.DirectImageTruncation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.CohomologyComparison
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Divisibility.Truncation

/-!
# Divisibility transfer for actual direct image

The native derived composition and truncation comparisons transfer divisibility
without asserting acyclicity of the positive higher direct images.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u dS dX dA

variable {S X : Scheme.{u}}
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- Scalar invertibility transfers from actual source cohomology and positive
higher direct images to actual derived sections of the original direct image. -/
theorem isIso_nsmul_homology_derivedGlobalSections_directImage
    (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} S) (n : ℕ)
    (hh : ∀ q : ℕ, 1 ≤ q → IsIso (n • 𝟙 ((higherDirectImage f q).obj L)))
    (i j : ℤ) (hij : i + 1 = j)
    [IsIso (n • 𝟙 ((homologyFunctor AddCommGrpCat.{u + 1} i).obj
      ((derivedGlobalSections S).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj L))))]
    [IsIso (n • 𝟙 ((homologyFunctor AddCommGrpCat.{u + 1} j).obj
      ((derivedGlobalSections S).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj L))))] :
    IsIso (n • 𝟙 ((homologyFunctor AddCommGrpCat.{u + 1} j).obj
      ((derivedGlobalSections X).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj
          ((directImage f).obj L))))) := by
  let A := (singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj L
  let K := (derivedDirectImage f).obj A
  have hK : ∀ k : ℤ, 1 ≤ k →
      IsIso (n • 𝟙 ((homologyFunctor (AbelianSheaf.{u, u + 1} X) k).obj K)) := by
    intro k hk
    lift k to ℕ using (by omega : 0 ≤ k) with q hq
    subst k
    let := hh q (by omega)
    exact nsmul_isIso_transport ((higherDirectImageIso.{u, dS, dX} f q).app L) n
  let : IsIso (n • 𝟙 ((homologyFunctor AddCommGrpCat.{u + 1} i).obj
      ((derivedGlobalSections X).obj K))) :=
    nsmul_isIso_transport ((homologyFunctor AddCommGrpCat.{u + 1} i).mapIso
      ((derivedDirectImageGlobalSectionsIso f).app A).symm) n
  let : IsIso (n • 𝟙 ((homologyFunctor AddCommGrpCat.{u + 1} j).obj
      ((derivedGlobalSections X).obj K))) :=
    nsmul_isIso_transport ((homologyFunctor AddCommGrpCat.{u + 1} j).mapIso
      ((derivedDirectImageGlobalSectionsIso f).app A).symm) n
  let := isIso_nsmul_id_homology_functor_truncLT
    (derivedGlobalSections X) K 1 n hK i j hij
  exact nsmul_isIso_transport ((homologyFunctor AddCommGrpCat.{u + 1} j).mapIso
    ((derivedGlobalSections X).mapIso (derivedDirectImageTruncLTOneIso f L))) n

end AlgebraicGeometry.Scheme.EtaleCohomology
