/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology.Shifted
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # Fixed-diagonal Serre transport through the original derived composition

Only the original homology window from zero through the requested degree is
used. The upper tail is removed by its native truncation arrow and preservation
of lower bounds. Serre closure applies to the finite original Postnikov layers;
no global upper cohomological bound or extra filtration model is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

universe u v d u' v' d' u'' v'' d''

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] (F : A ⥤ B) [F.Additive]
  (P : ObjectProperty B) [P.IsSerreClass]

/-- A finite diagonal on the actual homology of a nonnegative original object
supplies the Serre property of its requested derived-image homology. -/
theorem rightDerived_property_of_homology_diagonal
    (K : DerivedCategory.Plus A) [K.IsGE 0] (q : ℕ)
    (hdiag : ∀ j : ℕ, j ≤ q → P ((F.rightDerived (q - j)).obj
      ((DerivedCategory.Plus.homologyFunctor A (j : ℤ)).obj K))) :
    P ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj K)) := by
  let Q : ObjectProperty (DerivedCategory.Plus A) := fun N =>
    P ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj N))
  let : Q.IsClosedUnderIsomorphisms := {
    of_iso := fun e h => P.prop_of_iso
      ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).mapIso
        (F.rightDerivedFunctorPlus.mapIso e)) h }
  let : Q.ContainsZero := {
    exists_zero := ⟨0, isZero_zero _, P.prop_of_isZero
      ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map_isZero
        (F.rightDerivedFunctorPlus.map_isZero (isZero_zero _)))⟩ }
  let : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk'
    (P := Q) (fun T hT h₁ h₃ => by
      let U := DerivedCategory.Plus.ι.mapTriangle.obj
        (F.rightDerivedFunctorPlus.mapTriangle.obj T)
      have hU : U ∈ distTriang (DerivedCategory B) :=
        DerivedCategory.Plus.ι.map_distinguished _
          (F.rightDerivedFunctorPlus.map_distinguished T hT)
      exact P.prop_X₂_of_exact (DerivedCategory.HomologySequence.exact₂ U hU (q : ℤ)) h₁ h₃)
  let L := (DerivedCategory.Plus.TStructure.t.truncLT ((q : ℤ) + 1)).obj K
  let : L.IsGE 0 := by dsimp [L]; infer_instance
  let : L.IsLE (q : ℤ) :=
    DerivedCategory.Plus.TStructure.t.isLE_truncLT_obj K ((q : ℤ) + 1) q (by omega)
  have hL : Q L := by
    apply DerivedCategory.Plus.property_of_homology_bounds Q L 0 q
    intro i hi₀ hiq
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi₀
    have hj : j ≤ q := by omega
    have hcoeff : P ((F.rightDerived (q - j)).obj
        ((DerivedCategory.Plus.homologyFunctor A (j : ℤ)).obj L)) :=
      P.prop_of_iso ((F.rightDerived (q - j)).mapIso
        (DerivedCategory.Plus.homologyTruncLTIso K ((q : ℤ) + 1) j (by omega))).symm
        (hdiag j hj)
    have hsum : (j : ℤ) + ((q - j : ℕ) : ℤ) = (q : ℤ) := by omega
    have hsingle := P.prop_of_iso
      (F.rightDerivedSingleHomologyShiftedIso
        ((DerivedCategory.Plus.homologyFunctor A (j : ℤ)).obj L) j (q - j)).symm hcoeff
    simpa only [Q, hsum] using hsingle
  let T := (DerivedCategory.Plus.TStructure.t.triangleLTGE ((q : ℤ) + 1)).obj K
  have hT := DerivedCategory.Plus.TStructure.t.triangleLTGE_distinguished ((q : ℤ) + 1) K
  let : (F.rightDerivedFunctorPlus.obj T.obj₃).IsGE ((q : ℤ) + 1) :=
    F.rightDerivedFunctorPlus_isGE T.obj₃ ((q : ℤ) + 1)
  let : (F.rightDerivedFunctorPlus.mapTriangle.obj T).obj₃.IsGE ((q : ℤ) + 1) := by
    change (F.rightDerivedFunctorPlus.obj T.obj₃).IsGE ((q : ℤ) + 1)
    infer_instance
  have hIso : IsIso ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
      (F.rightDerivedFunctorPlus.map T.mor₁)) :=
    DerivedCategory.Plus.isIso_homology_mor₁_of_isGE
      (F.rightDerivedFunctorPlus.mapTriangle.obj T)
      (F.rightDerivedFunctorPlus.map_distinguished T hT) ((q : ℤ) + 1) q (by omega)
  exact P.prop_of_iso
    (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
      (F.rightDerivedFunctorPlus.map T.mor₁)) hIso) hL

variable {C : Type u''} [Category.{v''} C] [Abelian C] [HasDerivedCategory.{d''} C]
  [EnoughInjectives B]

/-- The original composition comparison transports the finite diagonal.
Preservation of injectives is a real hypothesis on the inner functor, not an
assumed comparison certificate or a cohomological-dimension bound. -/
theorem rightDerived_property_of_composition_diagonal
    (G : B ⥤ C) [G.Additive] [F.PreservesInjectiveObjects]
    (R : ObjectProperty C) [R.IsSerreClass] (M : A) (q : ℕ)
    (hdiag : ∀ j : ℕ, j ≤ q →
      R ((G.rightDerived (q - j)).obj ((F.rightDerived j).obj M))) :
    R (((F ⋙ G).rightDerived q).obj M) := by
  let K := F.rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor A 0).obj M)
  let : K.IsGE 0 := F.rightDerivedFunctorPlus_isGE _ 0
  have hK : R ((DerivedCategory.Plus.homologyFunctor C (q : ℤ)).obj
      (G.rightDerivedFunctorPlus.obj K)) := by
    apply G.rightDerived_property_of_homology_diagonal R K q
    intro j hj
    exact R.prop_of_iso ((G.rightDerived (q - j)).mapIso
      ((F.rightDerivedSingleHomologyIso j).app M)) (hdiag j hj)
  let H := DerivedCategory.Plus.homologyFunctor C (q : ℤ)
  let e := ((F ⋙ G).rightDerivedSingleHomologyIso q).app M ≪≫
    H.mapIso ((F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M))
  exact R.prop_of_iso e.symm hK

end CategoryTheory.Functor
