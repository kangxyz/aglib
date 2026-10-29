/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericDefectAcyclic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericHigherImages
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericSupportDivisibility
public import Aglib.AlgebraicGeometry.ResidueField.Constants

/-!
# Prime-to-characteristic Kummer cohomology of broad curves

These are original-map statements for arbitrary finite-type schemes of dimension
at most one over a separably closed field. No reducedness, smoothness, perfectness,
or general invariance of Gm under nilpotent or purely inseparable maps is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

attribute [local instance] hasSheafifyLarge

variable (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [CompactSpace X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include p

omit [CompactSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
private theorem closed_residue_isSepClosed (x : X) (hx : IsClosed ({x} : Set X)) :
    IsSepClosed (X.residueField x) := by
  let := residueAlgebra X p x
  let : Module.Finite k (X.residueField x) := residue_finite X p ⟨x, hx⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := X.residueField x)

/-- The original Gm power map is bijective in every degree at least two. -/
theorem power_bijective_of_curve (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Function.Bijective (Sheaf.H.map (power X n) q) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsNoetherian X := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (genericArtinLocus X)) := HasExt.standard _
  cases q with
  | zero => omega
  | succ q =>
    exact genericUnit_power_bijective.{u, u + 2, w} X n
      (fun r hr => genericKernel_subsingleton_H hdim (closed_residue_isSepClosed k X p) r hr)
      (fun r hr => genericCokernel_subsingleton_H hdim (closed_residue_isSepClosed k X p) r hr)
      (fun r hr => genericHigherImage_positive_nsmul_isIso X p hdim n hn hunit r hr)
      (fun r hr => genericArtin_power_bijective X p hdim n hn hunit r hr)
      q (by omega)

/-- Every original degree-two root class is the Kummer boundary of an ordinary Picard class. -/
theorem picardBoundary_surjective_of_curve (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Surjective (Kummer.picardBoundary X n hn hinv) :=
  Kummer.picardBoundary_surjective_of_power_injective X n hn hinv
    (power_bijective_of_curve k X p hdim n hn hunit 2 (by omega)).injective

/-- Original prime-to-characteristic root cohomology vanishes above degree two. -/
theorem roots_subsingleton_H_of_curve (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (mu X n) q) := by
  cases q with
  | zero => omega
  | succ q =>
    exact Kummer.roots_subsingleton_of_power_surjective_injective X n hn hinv q
      (power_bijective_of_curve k X p hdim n hn hunit q (by omega)).surjective
      (power_bijective_of_curve k X p hdim n hn hunit (q + 1) (by omega)).injective

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
