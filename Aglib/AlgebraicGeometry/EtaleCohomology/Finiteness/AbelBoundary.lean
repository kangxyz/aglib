/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.Naturality
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Properties
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! # The original Kummer class of the actual Abel family

The native smooth relative Cartier theorem supplies the graph-ideal input;
the native ideal-base-change and tensor-pullback theorems supply naturality.
No representability or divisor-rank oracle is retained in these statements.
The class is zero at the origin and its restriction is the original root
cohomology pullback. This is a family-class supplier, not Picard finiteness
or divisibility and not proper base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

attribute [local instance] hasSheafifyLarge

variable {S X T : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  (t : T ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (pullback p t))]

/-- The original boundary of the actual graph-difference line bundle. -/
def abelKummerBoundary (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(pullback p t, ⊤))) :
    Sheaf.H.{w} (mu (pullback p t) n) 2 :=
  Kummer.picardBoundary (pullback p t) n hn hinv
    (Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho t s hs)

/-- Actual dual evaluation trivializes the family at its origin. -/
theorem abelKummerBoundary_origin (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(pullback p t, ⊤))) :
    abelKummerBoundary p o ho t (t ≫ o) (by simp [Category.assoc, ho]) n hn hinv = 0 := by
  simp only [abelKummerBoundary, Hom.abelClass_origin, map_zero]

variable {T' : Scheme.{u}} (t' : T' ⟶ S) (a : T' ⟶ T) (ha : a ≫ t = t')
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p t'))]

/-- Pullback of the family class is the original root-cohomology map, with
independent original source and target Ext universes. -/
theorem abelKummerBoundary_baseChange (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(pullback p t, ⊤))) :
    Kummer.rootsCohomologyPullback (Hom.familyMap p t t' a ha) n hn hinv 2
        (abelKummerBoundary p o ho t s hs n hn hinv) =
      abelKummerBoundary p o ho t' (a ≫ s) (by rw [Category.assoc, hs, ha]) n hn
        (levelInvertible (Hom.familyMap p t t' a ha) n hinv) := by
  exact (Kummer.picardBoundary_pullback (Hom.familyMap p t t' a ha) n hn hinv
      (Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho t s hs)).trans
    (congrArg
      (Kummer.picardBoundary (pullback p t') n hn
        (levelInvertible (Hom.familyMap p t t' a ha) n hinv))
      (OverField.Curve.Abel.abelClass_baseChange Hom.smoothRelativeDivisorIdeal
        Hom.relativeCartierIdealBaseChange Modules.Invertible.moduleTensorPullback
        p o ho t t' s hs a ha))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
