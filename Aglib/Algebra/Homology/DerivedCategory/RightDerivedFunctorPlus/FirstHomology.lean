/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers

/-!
# The first layer under a left-exact right-derived functor

For an original complex with homology in degrees at least one, H1 of the
installed right-derived functor is the original functor applied to its H1.
The comparison uses the actual truncation inclusion, normalized native
single layer, original shift maps, and left-exact R0 comparison. No upper
bound on the complex or exactness of the original functor is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- The native degree-one single comparison uses the original shifts and
the actual left-exact degree-zero comparison. -/
def rightDerivedSingleHomologyOneIso (M : A) :
    (DerivedCategory.Plus.homologyFunctor B 1).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 1).obj M)) ≅
      F.obj M := by
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)
  let eShift : (DerivedCategory.Plus.homologyFunctor B 1).obj (K⟦(-1 : ℤ)⟧) ≅
      (DerivedCategory.Plus.homologyFunctor B 0).obj K := by
    change (DerivedCategory.homologyFunctor B 1).obj
        (DerivedCategory.Plus.ι.obj (K⟦(-1 : ℤ)⟧)) ≅
      (DerivedCategory.homologyFunctor B 0).obj (DerivedCategory.Plus.ι.obj K)
    let e := ((DerivedCategory.homologyFunctor B 0).shiftIso (-1) 1 0 (by omega)).app
      (DerivedCategory.Plus.ι.obj K)
    have e' : (DerivedCategory.homologyFunctor B 1).obj
        ((DerivedCategory.Plus.ι.obj K)⟦(-1 : ℤ)⟧) ≅
        (DerivedCategory.homologyFunctor B 0).obj (DerivedCategory.Plus.ι.obj K) := by
      simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using e
    exact (DerivedCategory.homologyFunctor B 1).mapIso
      ((DerivedCategory.Plus.ι.commShiftIso (-1)).app K) ≪≫ e'
  exact (DerivedCategory.Plus.homologyFunctor B 1).mapIso
      (F.rightDerivedFunctorPlus.mapIso
          (((DerivedCategory.Plus.singleFunctors A).shiftIso (-1) 1 0 (by omega)).app M).symm ≪≫
        (F.rightDerivedFunctorPlus.commShiftIso (-1)).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≪≫
    eShift ≪≫ F.rightDerivedSingleHomologyZeroIso.app M

/-- The first nonzero homology layer computes the first derived homology.
The forward map retains the inverse of the original truncation inclusion
on homology, followed by its normalized layer comparison. -/
def rightDerivedFirstHomologyIso (K : DerivedCategory.Plus A) [K.IsGE 1] :
    (DerivedCategory.Plus.homologyFunctor B 1).obj (F.rightDerivedFunctorPlus.obj K) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor A 1).obj K) := by
  let L := (DerivedCategory.Plus.TStructure.t.truncLT 2).obj K
  let T := (DerivedCategory.Plus.TStructure.t.triangleLTGE 2).obj K
  have hT := DerivedCategory.Plus.TStructure.t.triangleLTGE_distinguished 2 K
  let : L.IsGE 1 := by dsimp [L]; infer_instance
  let : L.IsLE 1 := DerivedCategory.Plus.TStructure.t.isLE_truncLT_obj K 2 1 (by omega)
  let : (F.rightDerivedFunctorPlus.obj T.obj₃).IsGE 2 :=
    F.rightDerivedFunctorPlus_isGE T.obj₃ 2
  let : (F.rightDerivedFunctorPlus.mapTriangle.obj T).obj₃.IsGE 2 := by
    change (F.rightDerivedFunctorPlus.obj T.obj₃).IsGE 2
    infer_instance
  let : IsIso ((DerivedCategory.Plus.homologyFunctor B 1).map
      (F.rightDerivedFunctorPlus.map T.mor₁)) :=
    DerivedCategory.Plus.isIso_homology_mor₁_of_isGE
      (F.rightDerivedFunctorPlus.mapTriangle.obj T)
      (F.rightDerivedFunctorPlus.map_distinguished T hT) 2 1 (by omega)
  let e : L ≅ (DerivedCategory.Plus.singleFunctor A 1).obj
      ((DerivedCategory.Plus.homologyFunctor A 1).obj K) :=
    DerivedCategory.Plus.isoSingleHomology L 1 ≪≫
      (DerivedCategory.Plus.singleFunctor A 1).mapIso
        (DerivedCategory.Plus.homologyTruncLTIso K 2 1 (by omega))
  exact (asIso ((DerivedCategory.Plus.homologyFunctor B 1).map
      (F.rightDerivedFunctorPlus.map T.mor₁))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor B 1).mapIso
      (F.rightDerivedFunctorPlus.mapIso e) ≪≫ F.rightDerivedSingleHomologyOneIso _

end CategoryTheory.Functor
