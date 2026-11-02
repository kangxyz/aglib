/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SerreLeray
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ShortExact

/-! # Serre transport backwards through the original Leray edge

The original positive truncation triangle recovers the image of H0 from the
image of the whole object and a strictly lower finite diagonal. No vanishing
of positive homology, extra filtration, or spectral-sequence model is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

universe u v d u' v' d'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] (F : A ⥤ B) [F.Additive]
  (P : ObjectProperty B) [P.IsSerreClass]

/-- A finite strictly positive diagonal of total degree n and the degree n+1
image of the original object supply the degree n+1 image of its actual H0. -/
theorem rightDerived_property_of_positive_diagonal
    (K : DerivedCategory.Plus A) [K.IsGE 0] (n : ℕ)
    (hdiag : ∀ j : ℕ, 0 < j → j ≤ n → P ((F.rightDerived (n - j)).obj
      ((DerivedCategory.Plus.homologyFunctor A (j : ℤ)).obj K)))
    (hwhole : P ((DerivedCategory.Plus.homologyFunctor B (n + 1 : ℕ)).obj
      (F.rightDerivedFunctorPlus.obj K))) :
    P ((F.rightDerived (n + 1)).obj
      ((DerivedCategory.Plus.homologyFunctor A 0).obj K)) := by
  let L := (DerivedCategory.Plus.TStructure.t.truncLT 1).obj K
  let N := (DerivedCategory.Plus.TStructure.t.truncGE 1).obj K
  let : L.IsGE 0 := by dsimp [L]; infer_instance
  let : L.IsLE 0 :=
    DerivedCategory.Plus.TStructure.t.isLE_truncLT_obj K 1 0 (by omega)
  let : N.IsGE 0 := by dsimp [N]; infer_instance
  let : N.IsGE 1 := by dsimp [N]; infer_instance
  have hN : P ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj N)) := by
    apply F.rightDerived_property_of_homology_diagonal P N n
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      exact P.prop_of_isZero ((F.rightDerived (n - 0)).map_isZero
        (DerivedCategory.Plus.isZero_homology_of_isGE N 1 0 (by omega)))
    · exact P.prop_of_iso ((F.rightDerived (n - j)).mapIso
        (DerivedCategory.Plus.homologyTruncGEIso K 1 j (by omega)))
        (hdiag j (by omega) hj)
  let T := (DerivedCategory.Plus.TStructure.t.triangleLTGE 1).obj K
  let U := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj T)
  have hU : U ∈ distTriang (DerivedCategory B) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished T
        (DerivedCategory.Plus.TStructure.t.triangleLTGE_distinguished 1 K))
  have hL : P ((DerivedCategory.Plus.homologyFunctor B (n + 1 : ℕ)).obj
      (F.rightDerivedFunctorPlus.obj L)) :=
    P.prop_X₂_of_exact
      (DerivedCategory.HomologySequence.exact₁ U hU (n : ℤ) (n + 1 : ℕ) (by omega))
      hN hwhole
  let e : L ≅ (DerivedCategory.Plus.singleFunctor A 0).obj
      ((DerivedCategory.Plus.homologyFunctor A 0).obj K) :=
    DerivedCategory.Plus.isoSingleHomology L 0 ≪≫
      (DerivedCategory.Plus.singleFunctor A 0).mapIso
        (DerivedCategory.Plus.homologyTruncLTIso K 1 0 (by omega))
  exact P.prop_of_iso ((DerivedCategory.Plus.homologyFunctor B (n + 1 : ℕ)).mapIso
    (F.rightDerivedFunctorPlus.mapIso e) ≪≫
      ((F.rightDerivedSingleHomologyIso (n + 1)).app
        ((DerivedCategory.Plus.homologyFunctor A 0).obj K)).symm) hL

end CategoryTheory.Functor
