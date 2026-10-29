/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClassification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteEtaleRigidity
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant

/-! # Finite constant coefficients and their original H1 maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u w w'

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable (A : Type u) [AddCommGroup A] [Finite A]

/-- The finite additive value in the native sheaf-value universe. -/
abbrev value : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} A)

/-- The actual native constant abelian sheaf with the displayed finite value. -/
abbrev coefficient (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X :=
  (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj (value A)

/-- The identity chart is an actual finite local trivialization of the constant sheaf. -/
def localTrivialization (X : Scheme.{u}) : FiniteLocalTrivialization (coefficient A X) where
  index := PUnit.{u + 1}
  chart _ := etaleTerminal X
  covers x := ⟨PUnit.unit, x, rfl⟩
  value _ := value A
  finite_value _ := inferInstance
  trivialization _ := (inverseImageConstantIso (𝟙 X)).app (value A)

/-- Finite constant coefficients are finite locally constant without an order condition. -/
theorem isFiniteLocallyConstant (X : Scheme.{u}) :
    IsFiniteLocallyConstant (coefficient A X) := ⟨localTrivialization A X⟩

/-- The literal constant cover represents the actual underlying finite constant set sheaf. -/
def setRepresentationIso (X : Scheme.{u}) :
    finiteRepresentedSetSheaf (Scheme.FiniteEtale.trivialCover X A) ≅
      underlyingSetSheaf (coefficient A X) :=
  Scheme.FiniteEtale.trivialCoverConstantIso X A ≪≫
    ((constantCommuteCompose (Scheme.smallEtaleTopology X)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app (value A)).symm

/-- The actual finite commutative group object on the literal constant cover. -/
def representation (X : Scheme.{u}) : CoefficientRepresentation (coefficient A X) :=
  ⟨CoefficientRepresentation.groupScheme _ _ (setRepresentationIso A X),
    inferInstance, inferInstance, inferInstance,
    CoefficientRepresentation.sheafIso _ _ (setRepresentationIso A X)⟩

variable {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The original H1 pullback followed by the canonical inverse-image constant isomorphism. -/
def pullbackH1 : H1Etale X (coefficient A X) →+ H1Etale S (coefficient A S) :=
  (coefficientMap ((inverseImageConstantIso f).app (value A)).hom).comp
    (h1Pullback f (coefficient A X))

omit [Finite A] in
/-- The finite constant map retains the literal original H1 map and coefficient transport. -/
theorem pullbackH1_apply (c : H1Etale X (coefficient A X)) :
    pullbackH1 A f c = coefficientMap ((inverseImageConstantIso f).app (value A)).hom
      (h1Pullback f (coefficient A X) c) := rfl

/-- Actual finite-etale fullness detects classes with finite constant coefficients. -/
theorem pullbackH1_injective_of_full [(Scheme.FiniteEtale.baseChange f).Full] :
    Function.Injective (pullbackH1 A f) := by
  apply Function.Injective.comp (coefficientIso
    ((inverseImageConstantIso f).app (value A))).injective
  exact FiniteEtaleRigidity.h1Pullback_injective_finite_of_full f
    (stacks03AJ X) (stacks03RV X) (stacks03AJ S) _ (isFiniteLocallyConstant A X)

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
