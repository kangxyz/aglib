/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-!
# The original low-degree right-derived edge

The positive truncation of a nonnegative object with no homology in degrees
`1,...,q-1` starts in degree `q`. Its right-derived image has the same lower
bound. The original unit triangle therefore gives a monomorphism in degree
`q`, without vanishing in degree `q` and without choosing a spectral sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory.Plus

universe u v d u' v' d' u'' v'' d''

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]

/-- Only the strictly intermediate positive homology groups are needed to
raise the lower bound of the original positive truncation. -/
theorem positiveTruncation_isGE_of_vanishing (K : Plus C) (q : ℕ)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q →
      IsZero ((homologyFunctor C (a : ℤ)).obj K)) :
    ((TStructure.t.truncGE 1).obj K).IsGE (q : ℤ) := by
  apply (isGE_ι_obj_iff _ _).mp
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  change IsZero ((homologyFunctor C i).obj ((TStructure.t.truncGE 1).obj K))
  by_cases h : i < 1
  · exact isZero_homology_of_isGE _ 1 i h
  · have hi₀ : 0 ≤ i := by omega
    have ha : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi₀
    have hz : IsZero ((homologyFunctor C i).obj K) := by
      simpa only [ha] using hvan i.toNat (by omega) (by omega)
    exact hz.of_iso (homologyTruncGEIso K 1 i (by omega)).symm

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{d} B]
  [EnoughInjectives B]
  {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{d'} C]
  (G : B ⥤ C) [G.Additive]

/-- The literal specified unit induces a mono after right derivation in the
first possibly nonzero positive degree. The degree-one hypothesis is empty. -/
theorem mono_homology_rightDerived_map_unit
    {M : B} {K : DerivedCategory.Plus B} [K.IsGE 0]
    (u : (singleFunctor B 0).obj M ⟶ K)
    [IsIso ((homologyFunctor B 0).map u)] (q : ℕ) (_hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q →
      IsZero ((homologyFunctor B (a : ℤ)).obj K)) :
    Mono ((homologyFunctor C (q : ℤ)).map (G.rightDerivedFunctorPlus.map u)) := by
  let T := unitTruncationTriangle u
  have hT := unitTruncationTriangle_distinguished u
  let : T.obj₃.IsGE (q : ℤ) := positiveTruncation_isGE_of_vanishing K q hvan
  let : (G.rightDerivedFunctorPlus.obj T.obj₃).IsGE (q : ℤ) :=
    G.rightDerivedFunctorPlus_isGE T.obj₃ q
  let V := G.rightDerivedFunctorPlus.mapTriangle.obj T
  have hV := G.rightDerivedFunctorPlus.map_distinguished T hT
  let : V.obj₃.IsGE (q : ℤ) := by
    change (G.rightDerivedFunctorPlus.obj T.obj₃).IsGE (q : ℤ)
    infer_instance
  have hz : IsZero ((homologyFunctor C ((q : ℤ) - 1)).obj V.obj₃) :=
    isZero_homology_of_isGE _ q ((q : ℤ) - 1) (by omega)
  exact ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
    V hV ((q : ℤ) - 1) q (by omega)).mpr (hz.eq_of_src _ _)

variable {A : Type u''} [Category.{v''} A] [Abelian A] [HasDerivedCategory.{d''} A]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- The original single-unit edge for two additive functors. Only the first
functor needs left exactness; no acyclicity or degree-q vanishing is assumed. -/
theorem mono_homology_rightDerived_singleUnit (M : A) (q : ℕ) (hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q → IsZero ((F.rightDerived a).obj M)) :
    Mono ((homologyFunctor C (q : ℤ)).map
      (G.rightDerivedFunctorPlus.map (F.rightDerivedSingleUnit M))) := by
  let K := F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj M)
  let : K.IsGE 0 := F.rightDerivedFunctorPlus_isGE _ 0
  let H := homologyFunctor B 0
  have he := F.rightDerivedSingleUnit_homology_zero M
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).symm.app (F.obj M)
  have : IsIso (e.hom ≫ H.map (F.rightDerivedSingleUnit M)) := by
    rw [show e.hom ≫ H.map (F.rightDerivedSingleUnit M) =
      F.rightDerivedSingleHomologyZeroIso.inv.app M from he]
    infer_instance
  let : IsIso (H.map (F.rightDerivedSingleUnit M)) :=
    IsIso.of_isIso_comp_left e.hom _
  apply G.mono_homology_rightDerived_map_unit (F.rightDerivedSingleUnit M) q hq
  intro a ha haq
  exact (hvan a ha haq).of_iso ((F.rightDerivedSingleHomologyIso a).app M).symm

end CategoryTheory.Functor
