/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceCohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality

/-! # The actual constant-source map for original chart cohomology -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w₁ w₂ w₃

namespace CategoryTheory.Sheaf

private theorem twoStep_ext {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasExt.{w₁} A] [HasExt.{w₂} B] [HasExt.{w₃} D]
    (R : A ⥤ B) (S : A ⥤ D) (T : B ⥤ D)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (τ : R ⋙ T ⟶ S) {X F : A} {Z : B} {W : D}
    (b : W ⟶ T.obj Z) (a : Z ⟶ R.obj X) {n : ℕ} (x : Ext.{w₁} X F n) :
    ((Ext.mk₀ b).comp
      (((Ext.mk₀ a).comp (x.mapExactFunctor R) (Nat.zero_add n)).mapExactFunctor T)
      (Nat.zero_add n)).comp (Ext.mk₀ (τ.app F)) (Nat.add_zero n) =
    (Ext.mk₀ (b ≫ T.map a ≫ τ.app X)).comp (x.mapExactFunctor S) (Nat.zero_add n) := by
  have h := SliceCohomology.extRestrictionCompatibility R S T τ b a
    (b ≫ T.map a ≫ τ.app X) (𝟙 X) (by simp) x
  simpa only [Ext.mk₀_id_comp] using h

private theorem twoStep_ext_of_eq {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasExt.{w₁} A] [HasExt.{w₂} B] [HasExt.{w₃} D]
    (R : A ⥤ B) (S : A ⥤ D) (T : B ⥤ D)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (τ : R ⋙ T ⟶ S) {X F : A} {Z : B} {W : D}
    (b : W ⟶ T.obj Z) (a : Z ⟶ R.obj X) {n : ℕ} (x : Ext.{w₁} X F n)
    (y : Ext.{w₂} Z (R.obj F) n) (z : Ext.{w₃} W (T.obj (R.obj F)) n)
    (v : Ext.{w₃} W (S.obj F) n)
    (hy : y = (Ext.mk₀ a).comp (x.mapExactFunctor R) (Nat.zero_add n))
    (hz : z = (Ext.mk₀ b).comp (y.mapExactFunctor T) (Nat.zero_add n))
    (hv : v = z.comp (Ext.mk₀ (τ.app F)) (Nat.add_zero n)) :
    v = (Ext.mk₀ (b ≫ T.map a ≫ τ.app X)).comp
      (x.mapExactFunctor S) (Nat.zero_add n) := by
  rw [hv, hz, hy]
  exact twoStep_ext R S T τ b a x

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The original constant-source map for the exact chart-site equivalence. -/
def chartSliceSource :
    ((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (etaleSliceSheafEquivalence U).inverse.obj
        (Sheaf.SliceCohomology.sliceIntegers.{u + 1, u, u + 1}
          (Scheme.smallEtaleTopology X) U) :=
  (etaleSliceSheafEquivalence U).toAdjunction.unit.app
    ((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
    (etaleSliceSheafEquivalence U).inverse.map
      ((etaleSliceConstantIso U).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The chart comparison source retains the actual two adjunction units and the
original inverse-image coefficient transport. -/
def chartComparisonSource :
    ((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (inverseImage U.hom).obj
        (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) U) :=
  chartSliceSource U ≫
    (etaleSliceSheafEquivalence U).inverse.map
      (Sheaf.SliceCohomology.sliceComparisonUnit.{u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) U) ≫
    (inverseImageEtaleIso U.hom).inv.app _

variable [hBaseExt : HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₂} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{w₃} (AbelianSheaf.{u, u + 1} U.left)]

local instance : HasExt.{w₁}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj U.right)) := hBaseExt

local instance : HasExt.{w₃}
    (Sheaf ((𝟭 Scheme.{u}).obj U.left).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hChartExt

/-- The accepted chart comparison is the original exact inverse-image Ext map,
precomposed with its actual constant-source map. -/
theorem originalCohomologyChartEquiv_apply (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w₁, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q U) :
    originalCohomologyChartEquiv U F q x =
      (Ext.mk₀ (chartComparisonSource U)).comp
        (x.mapExactFunctor (inverseImage U.hom)) (Nat.zero_add q) := by
  let R := (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U
  let : PreservesFiniteColimits R :=
    Sheaf.SliceCohomology.overPullback_preservesFiniteColimits
      (Scheme.smallEtaleTopology X) U
  let T := (etaleSliceSheafEquivalence U).inverse
  let : T.Additive := etaleSliceSheafEquivalence_inverse_additive U
  let a := Sheaf.SliceCohomology.sliceComparisonUnit.{u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U
  let y := Sheaf.SliceCohomology.sliceComparison.{w₁, w₂, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U F q x
  exact Sheaf.twoStep_ext_of_eq R (inverseImage U.hom) T
    (inverseImageEtaleIso U.hom).inv (chartSliceSource U) a x y
    (etaleSliceCohomologyEquiv U F q y) (originalCohomologyChartEquiv U F q x)
    (Sheaf.SliceCohomology.sliceComparison_apply.{w₁, w₂, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) U F q x)
    ((etaleSliceSheafEquivalence U).toAdjunction.sourceExtComparison_apply
      ((etaleSliceConstantIso U).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (F.over U) q y)
    rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
