/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.TensorPushforward
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.ThreeFactor

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/DerivedProjectionFormula.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 110]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The actual bounded-below derived projection formula

For an arbitrary scheme morphism and a finite locally free target coefficient,
derive the original ordinary projection-formula map. Local computation of the
source tensor functor and exactness of the target tensor functor give the two
canonical composite comparisons. Their original installed units satisfy the
literal projection-map square. Tensor is exact here, so the installed derived
tensor functors compute the original tensor on every bounded-below complex.
No quasicoherence or noetherian hypothesis is imposed on the input complex.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Standard original module-sheaf derived categories. -/
local instance derivedProjectionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules) [IsFiniteLocallyFree Y E]
/-- The canonical tensor/direct-image derived comparison. -/
def tensorPushforwardDerivedCompIso :
    (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
      Scheme.Modules.pushforward f).rightDerivedFunctorPlus ≅
    (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus ⋙
      derivedPushforwardPlus f := by
  let := tensorPushforward_isRightDerived f E
  exact rightDerivedUnique _ _
    (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
      Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit
    (Functor.rightDerivedFunctorPlusCompUnit
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
      (Scheme.Modules.pushforward f)) (CochainComplex.Plus.quasiIso X.Modules)
/-- This comparison retains the original tensor/direct-image composite unit. -/
theorem tensorPushforwardDerivedCompIso_unit (K : CochainComplex.Plus X.Modules) :
    (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
      Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app K ≫
      (tensorPushforwardDerivedCompIso f E).hom.app (DerivedCategory.Plus.Q.obj K) =
    (Functor.rightDerivedFunctorPlusCompUnit
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
      (Scheme.Modules.pushforward f)).app K := by
  let := tensorPushforward_isRightDerived f E
  simpa only [tensorPushforwardDerivedCompIso, rightDerivedUnique, rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    rightDerivedNatTrans_app
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
        Scheme.Modules.pushforward f).rightDerivedFunctorPlus
      ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus ⋙
        derivedPushforwardPlus f)
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
        Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit
      (Functor.rightDerivedFunctorPlusCompUnit
        (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
        (Scheme.Modules.pushforward f)) (CochainComplex.Plus.quasiIso X.Modules) (𝟙 _) K

local instance projectionFormulaSourceComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (Scheme.Modules.pushforward f) (moduleTensorLeftFunctor Y E)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance projectionFormulaTensorPushforwardIsRightDerived :
    ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus ⋙
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus).IsRightDerivedFunctor
        (Functor.rightDerivedFunctorPlusCompUnit
          (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
          (Scheme.Modules.pushforward f)) (CochainComplex.Plus.quasiIso X.Modules) :=
  tensorPushforward_isRightDerived f E

local instance projectionFormulaTargetComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
      (Scheme.Modules.pushforward f)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_isRightDerivedFunctor _ _

/-- The derived projection formula induced by the original ordinary projection map. -/
def derivedProjectionFormulaIso :
    derivedPushforwardPlus f ⋙ (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlus ≅
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus ⋙
        derivedPushforwardPlus f :=
  Functor.rightDerivedFunctorPlusThreeFactorIso
    (Scheme.Modules.pushforward f) (moduleTensorLeftFunctor Y E)
    (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
    (Scheme.Modules.pushforward f) (projectionFormulaNatIso f E)

/-- The shared constructor retains the original projection map and selected tensor comparison. -/
theorem derivedProjectionFormulaIso_eq_original :
    derivedProjectionFormulaIso f E =
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (moduleTensorLeftFunctor Y E)).symm ≪≫
      (Scheme.Modules.pushforward f ⋙ moduleTensorLeftFunctor Y E).rightDerivedFunctorPlusIso
        (projectionFormulaNatIso f E) ≪≫ tensorPushforwardDerivedCompIso f E := by
  have hR : Functor.rightDerivedFunctorPlusCompIso
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
      (Scheme.Modules.pushforward f) = tensorPushforwardDerivedCompIso f E := by
    exact Functor.rightDerivedFunctorPlusCompIso_eq_rightDerivedUnique _ _
  rw [derivedProjectionFormulaIso, Functor.rightDerivedFunctorPlusThreeFactorIso,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_preservesHomology, hR]

/-- Both original composite units and the literal ordinary projection formula are retained. -/
theorem derivedProjectionFormulaIso_unit (K : CochainComplex.Plus X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward f) (moduleTensorLeftFunctor Y E)).app K ≫
      (derivedProjectionFormulaIso f E).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
      ((NatIso.mapCochainComplexPlus (projectionFormulaNatIso f E)).hom.app K) ≫
    (Functor.rightDerivedFunctorPlusCompUnit
      (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
      (Scheme.Modules.pushforward f)).app K := by
  exact Functor.rightDerivedFunctorPlusThreeFactorIso_unit_app
    (Scheme.Modules.pushforward f) (moduleTensorLeftFunctor Y E)
    (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
    (Scheme.Modules.pushforward f) (projectionFormulaNatIso f E) K
end AlgebraicGeometry.Scheme.Modules
