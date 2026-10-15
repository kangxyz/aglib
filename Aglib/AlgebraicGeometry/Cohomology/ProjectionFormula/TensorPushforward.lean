/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.LocalDerivedPushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.InjectiveRestriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/TensorDerivedPushforward.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 90]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Actual derived direct image of tensor with pulled-back bundles

Tensor with a finite locally free sheaf is exact through its original short
exact maps, so its installed derived unit is invertible on every bounded-below
complex. Local injectivity on inverse images of affine target charts proves
that tensoring an injective-term complex computes its original direct image.
The original composite unit therefore genuinely derives tensor then pushforward.
The morphism is arbitrary, and there is no upper-bound hypothesis.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Standard original derived categories of module sheaves. -/
local instance tensorProjectionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- The exact tensor functor computes its installed derived functor on every complex. -/
theorem isIso_moduleTensorLeft_derivedUnit {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] :
    IsIso (moduleTensorLeftFunctor X E).rightDerivedFunctorPlusUnit :=
  (moduleTensorLeftFunctor X E).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
/-- Tensoring an injective-term bounded-below complex with a pulled-back bundle computes
its actual original direct image. -/
theorem isIso_derivedPushforwardPlusUnit_tensor_injective {X Y : Scheme.{u}}
    (f : X ⟶ Y) (E : Y.Modules) [IsFiniteLocallyFree Y E]
    (K : CochainComplex.Plus X.Modules) (hK : ∀ n, Injective (K.obj.X n)) :
    IsIso ((derivedPushforwardPlusUnit f).app
      ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus.obj
        K)) := by
  apply isIso_derivedPushforwardPlusUnit_of_locally_flasque f
    Y.affineBasisCover.X Y.affineBasisCover.f
    (fun y => ⟨Y.affineBasisCover.idx y, Y.affineBasisCover.covers y⟩)
  intro i n
  let := hK n
  let j := Y.affineBasisCover.f i
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (Y.affineBasisCover.f i))
  let : Injective (((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj
      (K.obj.X n)).restrict (pullback.fst f j)) :=
    tensor_pullback_restrict_injective f (Y.affineBasisCoverRing i) j E (K.obj.X n)
  exact inferInstanceAs (TopCat.Presheaf.IsFlasque
    ((((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj
      (K.obj.X n)).restrict (pullback.fst f j)).presheaf))
/-- The actual derived tensor followed by direct image derives the original composite. -/
theorem tensorPushforward_isRightDerived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] :
    ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus ⋙
      derivedPushforwardPlus f).IsRightDerivedFunctor
        (Functor.rightDerivedFunctorPlusCompUnit
          (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E))
          (Scheme.Modules.pushforward f)) (CochainComplex.Plus.quasiIso X.Modules) := by
  let T := moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)
  let F := Scheme.Modules.pushforward f
  apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
    (T ⋙ F)).isRightDerivedFunctor_of_isIso
  intro J
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  change IsIso (F.rightDerivedFunctorPlusUnit.app (T.mapCochainComplexPlus.obj
    ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)) ≫
    F.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)))
  have : IsIso (F.rightDerivedFunctorPlusUnit.app (T.mapCochainComplexPlus.obj
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J))) :=
    isIso_derivedPushforwardPlusUnit_tensor_injective f E _ (fun n =>
      inferInstanceAs (Injective (J.obj.X n).obj))
  infer_instance
end AlgebraicGeometry.Scheme.Modules
