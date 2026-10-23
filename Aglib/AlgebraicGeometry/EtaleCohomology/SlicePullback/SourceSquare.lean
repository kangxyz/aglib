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
      Sheaf.ModuleCoefficients.constantHomSectionsEquiv (etaleTerminalIsTerminal U.left) A a := by
  let c := constantSheafAdj ((Scheme.smallEtaleTopology X).over U)
    AddCommGrpCat.{u + 1} Over.mkIdTerminal
  let d := constantAdjunction U.left
  let R := (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse
  let e := (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).toAdjunction
  have h : (c.comp e).homEquiv _ A
      (((sliceConstantSheafIso.{u, u + 1} U).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ a) =
      d.homEquiv _ A a := by
    rw [Adjunction.homEquiv_naturality_right]
    change (c.comp e).homEquiv _ _ (((c.comp e).leftAdjointUniq d).hom.app _) ≫
      (globalSections U.left).map a = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact (Adjunction.homEquiv_unit d _ _ a).symm
  have h' := congrArg (fun k => k (ULift.up (1 : ℤ))) h
  change (c.homEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (R.obj A)
    (sliceIntegerSource U ≫ R.map a)) (ULift.up (1 : ℤ)) =
      (d.homEquiv _ A a) (ULift.up (1 : ℤ))
  refine Eq.trans ?_ h'
  have hq : sliceIntegerSource U ≫
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.map a =
      e.homEquiv _ A (((sliceConstantSheafIso.{u, u + 1} U).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ a) := by
    change (e.unit.app _ ≫ R.map _) ≫ R.map a =
      e.unit.app _ ≫ R.map (_ ≫ a)
    exact (Category.assoc _ _ _).trans
      (congrArg (fun k => e.unit.app _ ≫ k) (R.map_comp _ a).symm)
  have hcomp := congrArg
    (fun k => (k (AddCommGrpCat.of (ULift.{u + 1} ℤ)) A
      (((sliceConstantSheafIso.{u, u + 1} U).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ a)) (ULift.up (1 : ℤ)))
    (Adjunction.comp_homEquiv c e)
  have heval := congrArg
    (fun k : sliceIntegers.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U ⟶ R.obj A =>
      (c.homEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (R.obj A) k)
        (ULift.up (1 : ℤ))) hq
  exact heval.trans hcomp.symm

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
        (representedIntegerAugmentation U) := by
  let J := Scheme.smallEtaleTopology X
  let Z := (constantSheaf J AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let z := Sheaf.ModuleCoefficients.constantHomSectionsEquiv
    (etaleTerminalIsTerminal X) Z (𝟙 Z)
  let β : U ⟶ (siteEtalePostcompose U.hom).obj (etaleTerminal U.left) :=
    ((Scheme.Etale.sliceEquivalence U).unitIso.app (Over.mk (𝟙 U))).hom.left
  apply (sliceSectionsAddEquiv.{u + 1, u, u + 1} J _).injective
  rw [← Category.assoc, sliceSections_postcomp, sliceIntegerSource_sections,
    sliceSections_postcomp]
  have hgen : sliceSectionsAddEquiv.{u + 1, u, u + 1} J
      ((freeAbelianSheaf.{u + 1} J U).over U)
      (sliceComparisonUnit.{u + 1, u, u + 1} J U) =
      sectionsAddEquiv.{u + 1} J U (freeAbelianSheaf.{u + 1} J U) (𝟙 _) :=
    sliceComparisonUnit_generator J U
  rw [hgen]
  have hc := constantTransport_homEquiv U.hom (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (𝟙 Z)
  let a := ((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv
  have ha : a ≫ (inverseImage U.hom).map (𝟙 Z) = a :=
    (congrArg (fun k => a ≫ k) ((inverseImage U.hom).map_id Z)).trans
      (Category.comp_id a)
  have hc' := (congrArg ((constantAdjunction U.left).homEquiv
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ((inverseImage U.hom).obj Z)) ha).symm.trans hc
  have hcz := congrArg (fun k => k (ULift.up (1 : ℤ))) hc'
  change Sheaf.ModuleCoefficients.constantHomSectionsEquiv (etaleTerminalIsTerminal U.left)
    ((inverseImage U.hom).obj Z)
      (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) =
      globalSectionsPullback U.hom Z z at hcz
  refine (congrArg
    (((inverseImageSliceInverseIso U).hom.app Z).hom.app (op (Over.mk (𝟙 U))))
    hcz).trans ?_
  change Z.obj.map β.op
      (((inverseImageEtaleIso U.hom).hom.app Z).hom.app (op (etaleTerminal U.left))
        (globalSectionsPullback U.hom Z z)) =
    (representedIntegerAugmentation U).hom.app (op U)
      (sectionsEquiv.{u + 1} J U (freeAbelianSheaf.{u + 1} J U) (𝟙 _))
  have hg := congrArg (fun k => k z) (globalSectionsPullback_etaleRestriction U.hom Z)
  change ((inverseImageEtaleIso U.hom).hom.app Z).hom.app (op (etaleTerminal U.left))
      (globalSectionsPullback U.hom Z z) = _ at hg
  refine (congrArg (Z.obj.map β.op) hg).trans ?_
  have ht : β ≫ (etaleTerminalIsTerminal X).from
      ((siteEtalePostcompose U.hom).obj (etaleTerminal U.left)) =
      (etaleTerminalIsTerminal X).from U := (etaleTerminalIsTerminal X).hom_ext _ _
  have hm := congrArg (fun k => k z) (Z.obj.map_comp
    ((etaleTerminalIsTerminal X).from
      ((siteEtalePostcompose U.hom).obj (etaleTerminal U.left))).op β.op)
  refine hm.symm.trans ?_
  refine (congrArg (fun k : U ⟶ etaleTerminal X => Z.obj.map k.op z) ht).trans ?_
  let e := constantIntegerFreeTerminalIso.{u + 1, u, u + 1} J (etaleTerminalIsTerminal X)
  have hz := constantIntegerFreeTerminalIso_evaluation J (etaleTerminalIsTerminal X) Z e.inv
  have hz' : z = sectionsEquiv.{u + 1} J (etaleTerminal X) Z e.inv :=
    (congrArg (Sheaf.ModuleCoefficients.constantHomSectionsEquiv
      (etaleTerminalIsTerminal X) Z) e.hom_inv_id).symm.trans hz
  have hpre := freeSections_naturality J
    ((etaleTerminalIsTerminal X).from U) Z e.inv
  have hrep := sectionsEquiv_naturality J U
    (𝟙 (freeAbelianSheaf.{u + 1} J U)) (representedIntegerAugmentation U)
  have hid := congrArg (sectionsEquiv.{u + 1} J U Z)
    (Category.id_comp (representedIntegerAugmentation U))
  exact (congrArg (Z.obj.map ((etaleTerminalIsTerminal X).from U).op) hz').trans
    (hpre.symm.trans (hid.symm.trans hrep))

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
  have h := extRestrictionCompatibility.{w₀, w₁, w₂}
    (A := AbelianSheaf.{u, u + 1} X) (B := AbelianSheaf.{u, u + 1} U.left)
    (D := Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})
    (inverseImage (X := X) (S := U.left) U.hom)
    ((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U)
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse
    (inverseImageSliceInverseIso U).hom (sliceIntegerSource U)
    (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (sliceComparisonUnit.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) U)
    (representedIntegerAugmentation U) (inverseImageSlice_source_square U) x
  rw [sliceCohomologyEquiv, Adjunction.sourceExtComparison_apply,
    cohomologyPullback_apply, sliceComparison_apply]
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

end AlgebraicGeometry.Scheme.EtaleCohomology
