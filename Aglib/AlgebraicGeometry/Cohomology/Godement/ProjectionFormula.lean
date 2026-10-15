/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total
public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementProjectionFormula.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 212]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Original projection formula followed by original Godement augmentation

The literal ordinary finite locally free projection formula, followed by the
original augmentation into the Godement total, is a natural quasi-isomorphism
on every lower-bounded complex with flasque terms. Its localized map is the
original installed derived projection formula with the actual installed units
and Godement comparison. There is no tensor-flasqueness premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The standard derived-category model for module sheaves on `X` in projection-formula
comparisons. -/
local instance godementProjectionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules) [IsFiniteLocallyFree Y E]

/-- The original ordinary projection formula on original lower-bounded complexes. -/
def projectionFormulaPlusIso :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (moduleTensorLeftFunctor Y E).mapCochainComplexPlus ≅
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward f).mapCochainComplexPlus :=
  (mapCochainComplexPlusCompIso (Scheme.Modules.pushforward f)
    (moduleTensorLeftFunctor Y E)).symm ≪≫
    NatIso.mapCochainComplexPlus (projectionFormulaNatIso f E) ≪≫
    mapCochainComplexPlusCompIso
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
      (Scheme.Modules.pushforward f)

/-- This component is literally the original projection-formula map in every degree. -/
theorem projectionFormulaPlusIso_hom_f (C : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((projectionFormulaPlusIso f E).hom.app C).hom.f n =
      projectionFormulaMap f E (C.obj.X n) := by
  rfl

/-- The two original termwise-composition comparisons are identity maps on components. -/
theorem projectionFormulaPlusIso_hom_app (C : CochainComplex.Plus X.Modules) :
    (projectionFormulaPlusIso f E).hom.app C =
      (NatIso.mapCochainComplexPlus (projectionFormulaNatIso f E)).hom.app C := by
  apply ObjectProperty.hom_ext
  ext n
  rfl

/-- The literal original ordinary projection formula followed by the original total unit. -/
def godementProjectionFormulaMap :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (moduleTensorLeftFunctor Y E).mapCochainComplexPlus ⟶
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus ⋙
        godementTotalPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus :=
  (projectionFormulaPlusIso f E).hom ≫
    whiskerLeft
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus
      (whiskerRight (godementTotalPlusUnit X)
        (Scheme.Modules.pushforward f).mapCochainComplexPlus)

/-- The original source comparison uses the tensor unit before the direct-image unit. -/
def godementProjectionFormulaSourceComparison (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj
        ((moduleTensorLeftFunctor Y E).mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj C)) ⟶
      (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlus.obj
        ((derivedPushforwardPlus f).obj (DerivedCategory.Plus.Q.obj C)) :=
  (Functor.rightDerivedFunctorPlusCompUnit
    (Scheme.Modules.pushforward f) (moduleTensorLeftFunctor Y E)).app C

/-- The original target comparison uses the total comparison before the exact tensor unit. -/
def godementProjectionFormulaTargetComparison (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj
          ((godementTotalPlus X).obj
            ((moduleTensorLeftFunctor X
              ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus.obj C))) ⟶
      (derivedPushforwardPlus f).obj
        ((moduleTensorLeftFunctor X
          ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj C)) :=
  (godementTotalDerivedPushforwardIso f).hom.app
      ((moduleTensorLeftFunctor X
        ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus.obj C) ≫
    (derivedPushforwardPlus f).map
      ((moduleTensorLeftFunctor X
        ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlusUnit.app C)

/-- Pushing the actual augmentation, then applying the actual total comparison,
gives exactly the original installed direct-image unit on the input. -/
theorem godementTotalDerivedPushforwardIso_source_unit (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
          ((godementTotalPlusUnit X).app C)) ≫
      (godementTotalDerivedPushforwardIso f).hom.app C =
        (derivedPushforwardPlusUnit f).app C := by
  have h := (derivedPushforwardPlusUnit f).naturality ((godementTotalPlusUnit X).app C)
  apply (cancel_mono ((godementTotalDerivedAugmentation f).app C)).1
  simp only [godementTotalDerivedPushforwardIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  change _ ≫ ((asIso (godementTotalDerivedUnit f)).hom.app C ≫
    ((asIso (godementTotalDerivedAugmentation f)).inv.app C ≫
      (asIso (godementTotalDerivedAugmentation f)).hom.app C)) = _
  rw [Iso.inv_hom_id_app, Category.comp_id]
  exact h

/-- The localized literal arrow is exactly the original derived projection-formula mate,
with the installed units and the original Godement comparison in the displayed order. -/
theorem godementProjectionFormulaMap_derived (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((godementProjectionFormulaMap f E).app C) ≫
        godementProjectionFormulaTargetComparison f E C =
      godementProjectionFormulaSourceComparison f E C ≫
        (derivedProjectionFormulaIso f E).hom.app (DerivedCategory.Plus.Q.obj C) := by
  dsimp only [godementProjectionFormulaMap, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, godementProjectionFormulaTargetComparison]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (DerivedCategory.Plus.Q.map
    ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
      ((godementTotalPlusUnit X).app _))) _ _]
  rw [godementTotalDerivedPushforwardIso_source_unit]
  rw [projectionFormulaPlusIso_hom_app]
  simpa only [godementProjectionFormulaSourceComparison,
    Functor.rightDerivedFunctorPlusCompUnit_app, derivedPushforwardPlusUnit,
    derivedPushforwardPlus, Category.assoc] using
    (derivedProjectionFormulaIso_unit f E C).symm

theorem godementProjectionFormulaTargetComparison_isIso
    (C : CochainComplex.Plus X.Modules) :
    IsIso (godementProjectionFormulaTargetComparison f E C) := by
  let : IsFiniteLocallyFree X ((Scheme.Modules.pullback f).obj E) :=
    finiteLocallyFree_pullback f E
  let := isIso_moduleTensorLeft_derivedUnit ((Scheme.Modules.pullback f).obj E)
  let : IsIso
      ((moduleTensorLeftFunctor X
        ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlusUnit.app C) := by
    exact inferInstanceAs (IsIso
      ((moduleTensorLeftFunctor X
        ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlusUnit.app C))
  let : IsIso ((derivedPushforwardPlus f).map
      ((moduleTensorLeftFunctor X
        ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlusUnit.app C)) := by
    infer_instance
  dsimp only [godementProjectionFormulaTargetComparison]
  exact IsIso.comp_isIso'
    ((godementTotalDerivedPushforwardIso f).app
      ((moduleTensorLeftFunctor X
        ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus.obj C)).isIso_hom
    (Functor.map_isIso (derivedPushforwardPlus f) _)

/-- Flasque terms make the actual original source comparison invertible. -/
theorem godementProjectionFormulaSourceComparison_isIso
    (C : CochainComplex.Plus X.Modules)
    (hC : ∀ n, TopCat.Presheaf.IsFlasque (C.obj.X n).presheaf) :
    IsIso (godementProjectionFormulaSourceComparison f E C) := by
  let := isIso_moduleTensorLeft_derivedUnit E
  let := isIso_derivedPushforwardPlusUnit_of_flasque f C hC
  dsimp only [godementProjectionFormulaSourceComparison]
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  change IsIso ((moduleTensorLeftFunctor Y E).rightDerivedFunctorPlusUnit.app
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj C) ≫
    (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlus.map
      ((derivedPushforwardPlusUnit f).app C))
  infer_instance

/-- Original D+ localization reflects quasi-isomorphisms of the original Plus morphisms. -/
theorem quasiIso_of_isIso_plusQ {Z : Scheme.{u}}
    {C D : CochainComplex.Plus Z.Modules} (a : C ⟶ D)
    [IsIso (DerivedCategory.Plus.Q.map a)] : QuasiIso a.hom := by
  have h := (DerivedCategory.Plus.QCompιIso Z.Modules).hom.naturality a
  have hcomp : IsIso
      ((CochainComplex.Plus.ι Z.Modules ⋙ DerivedCategory.Q).map a) := by
    have : IsIso
        ((DerivedCategory.Plus.QCompιIso Z.Modules).hom.app C ≫
          (CochainComplex.Plus.ι Z.Modules ⋙ DerivedCategory.Q).map a) := by
      rw [← h]
      exact inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map a) ≫
          (DerivedCategory.Plus.QCompιIso Z.Modules).hom.app D))
    exact IsIso.of_isIso_comp_left ((DerivedCategory.Plus.QCompιIso Z.Modules).hom.app C) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso Z.Modules a.hom).mp hcomp

/-- Every lower-bounded termwise flasque input has the original weak projection-formula arrow.
No upper bound, quasicoherence, perfectness, or tensor-flasqueness premise is used. -/
theorem godementProjectionFormulaMap_quasiIso
    (C : CochainComplex.Plus X.Modules)
    (hC : ∀ n, TopCat.Presheaf.IsFlasque (C.obj.X n).presheaf) :
    QuasiIso ((godementProjectionFormulaMap f E).app C).hom := by
  let := godementProjectionFormulaSourceComparison_isIso f E C hC
  let := godementProjectionFormulaTargetComparison_isIso f E C
  have hcomp : IsIso
      (DerivedCategory.Plus.Q.map ((godementProjectionFormulaMap f E).app C) ≫
        godementProjectionFormulaTargetComparison f E C) := by
    rw [godementProjectionFormulaMap_derived]
    infer_instance
  let : IsIso (DerivedCategory.Plus.Q.map ((godementProjectionFormulaMap f E).app C)) :=
    IsIso.of_isIso_comp_right _ (godementProjectionFormulaTargetComparison f E C)
  exact quasiIso_of_isIso_plusQ _

end AlgebraicGeometry.Scheme.Modules.Godement
