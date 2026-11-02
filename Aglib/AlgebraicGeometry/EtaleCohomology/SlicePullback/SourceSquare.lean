/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback

/-! # The original integer-source square for etale pullback

Both source identifications are the existing adjunction comparisons. Evaluation
at the genuine terminal slice object identifies them with the represented
augmentation, normalized by the original constant-integer/free-terminal iso.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sheaf.Hypercohomology CategoryTheory.Sheaf.SliceCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w₀ w₁ w₂

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The original inverse image, transported back to the actual slice. -/
def inverseImageSliceInverseIso :
    inverseImage U.hom ⋙ (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse ≅
      (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U :=
  Functor.isoWhiskerRight (inverseImageSliceIso U)
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse ≪≫
    Functor.isoWhiskerLeft ((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U)
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).unitIso.symm

/-- Source map of the already constructed scheme/slice cohomology equivalence. -/
def sliceIntegerSource :
    sliceIntegers.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U ⟶
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj
        ((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).unitIso.hom.app _ ≫
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.map
      ((sliceConstantSheafIso.{u, u + 1} U).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The equivalence-adjunction source map preserves the original integer one. -/
theorem sliceIntegerSource_sections (A : AbelianSheaf.{u, u + 1} U.left)
    (a : (constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ A) :
    sliceSectionsAddEquiv.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) _
      (sliceIntegerSource U ≫
        (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.map a) =
      Sheaf.ModuleCoefficients.constantHomSectionsEquiv (etaleTerminalIsTerminal U.left) A a :=
  Sheaf.SliceCohomology.originalSliceIntegerSource_sections.{u + 1, u, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U (Scheme.smallEtaleTopology U.left)
    (Scheme.Etale.sliceEquivalence U) (etaleTerminalIsTerminal U.left) A a

/-- The represented augmentation with exactly the original integer-source normalization. -/
def representedIntegerAugmentation :
    freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) U ⟶
      (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
    ((etaleTerminalIsTerminal X).from U) ≫
      (constantIntegerFreeTerminalIso (Scheme.smallEtaleTopology X)
        (etaleTerminalIsTerminal X)).inv

/-- Literal source square comparing the original scheme inverse-image source
with the actual represented augmentation on the original slice. -/
theorem inverseImageSlice_source_square :
    sliceIntegerSource U ≫
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.map
        (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) ≫
      (inverseImageSliceInverseIso U).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
    sliceComparisonUnit.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U ≫
      ((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U).map
        (representedIntegerAugmentation U) :=
  by
  let : ((Scheme.Etale.sliceEquivalence U).inverse ⋙ Over.forget U).IsContinuous
      (Scheme.smallEtaleTopology U.left) (Scheme.smallEtaleTopology X) := by
    change (siteEtalePostcompose U.hom).IsContinuous
      (Scheme.smallEtaleTopology U.left) (Scheme.smallEtaleTopology X)
    exact siteEtalePostcompose_continuous U.hom
  exact Sheaf.SliceCohomology.originalInverseImageSlice_source_square.{u + 1, u, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U (Scheme.smallEtaleTopology U.left)
    (Scheme.Etale.sliceEquivalence U) (siteBaseChange U.hom)
    (siteEtalePostcomposeAdj U.hom) (inverseImageAdjunction U.hom)
    (etaleTerminalIsTerminal X) (etaleTerminalIsTerminal U.left)
    (siteBaseChangeTerminalIso U.hom) (inverseImageConstantIso U.hom)
    (inverseImageConstantCanonicalIso_eq U.hom).symm

section Cohomology

variable [HasExt.{w₀} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} U.left)]
  [HasExt.{w₂} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})]

/-- The all-degree square for the original scheme pullback and the original
represented restriction, with independent base, chart, and slice Ext universes. -/
theorem cohomologyPullback_sliceComparison (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
    (x : Sheaf.H.{w₀} F n) :
    Sheaf.H.map ((inverseImageSliceInverseIso U).hom.app F) n
      (sliceCohomologyEquiv.{u, u + 1, w₂, w₁} U ((inverseImage U.hom).obj F) n
        (cohomologyPullback.{u, w₀, w₁} (X := X) (S := U.left) U.hom F n x)) =
    sliceComparison.{w₀, w₂, u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U F n
      ((Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add n)) := by
  let := overPullback_preservesFiniteColimits.{u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U
  have h := sourceExtComparison_compatibility
    (inverseImage (X := X) (S := U.left) U.hom)
    ((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U)
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).toAdjunction
    ((sliceConstantSheafIso.{u, u + 1} U).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImageSliceInverseIso U)
    (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (sliceComparisonUnit.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U)
    (representedIntegerAugmentation U) (inverseImageSlice_source_square U) x
  rw [sliceCohomologyEquiv, cohomologyPullback_apply, sliceComparison_apply]
  exact h

/-- Injectivity of literal represented restriction implies injectivity of the
original scheme pullback, without replacing the coefficient or cohomology. -/
theorem cohomologyPullback_injective_of_represented_precomp
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
    (hinj : Function.Injective (fun x : Sheaf.H.{w₀} F n =>
      (Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add n))) :
    Function.Injective (cohomologyPullback.{u, w₀, w₁} (X := X) (S := U.left) U.hom F n) := by
  intro x y hxy
  apply hinj
  apply (sliceComparison.{w₀, w₂, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U F n).injective
  rw [← cohomologyPullback_sliceComparison, ← cohomologyPullback_sliceComparison, hxy]

end Cohomology

section ZeroTransfer

variable [HasExt.{w₀} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} U.left)]

/-- Vanishing under the original represented augmentation implies vanishing
under the original geometric pullback, through the proved integer-source square. -/
theorem cohomologyPullback_eq_zero_of_represented_precomp_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (x : Sheaf.H.{w₀} F n)
    (hx : (Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add n) = 0) :
    cohomologyPullback.{u, w₀, w₁} (X := X) (S := U.left) U.hom F n x = 0 := by
  let := overPullback_preservesFiniteColimits.{u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U
  rw [cohomologyPullback_apply]
  exact extPrecomp_eq_zero_of_precomp_eq_zero
    (inverseImage (X := X) (S := U.left) U.hom)
    ((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U)
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).toAdjunction
    ((sliceConstantSheafIso.{u, u + 1} U).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImageSliceInverseIso U)
    (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (sliceComparisonUnit.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U)
    (representedIntegerAugmentation U) (inverseImageSlice_source_square U) x hx

end ZeroTransfer

end AlgebraicGeometry.Scheme.EtaleCohomology
