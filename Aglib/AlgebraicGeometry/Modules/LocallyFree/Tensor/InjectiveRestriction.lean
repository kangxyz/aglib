/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorInjectiveRetract
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Retract
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/TensorInjectiveRestriction.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 62]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Injective tensor on inverse images of affine target charts

An affine vector bundle has an actual finite-free retraction. Pulling that
retraction back shows that its tensor sends an injective sheaf to an injective
sheaf. The original cartesian pullback mate and tensor restriction comparison
then give injectivity over inverse images of affine target charts. No global
injectivity assertion for arbitrary locally free coefficients is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Pulled-back affine bundle coefficients retain injectivity through their actual free retract. -/
theorem tensor_pullback_affine_injective {X : Scheme.{u}} (R : CommRingCat.{u})
    (f : X ⟶ Spec R) (E : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) E]
    (M : X.Modules) [Injective M] :
    Injective ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M) := by
  obtain ⟨I, hI, ⟨h⟩⟩ := exists_retract_finiteFree R E
  let := hI
  exact tensor_injective_of_retract_finiteFree X.sheaf I (pullbackFiniteFreeRetract f h) M
/-- The actual restricted tensor is injective above an affine target chart. -/
theorem tensor_pullback_restrict_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : CommRingCat.{u}) (j : Spec R ⟶ Y) [IsOpenImmersion j]
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (M : X.Modules) [Injective M] :
    Injective (((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M).restrict
      (pullback.fst f j)) := by
  let a := pullback.fst f j
  let b := pullback.snd f j
  let W := CategoryTheory.Limits.pullback f j
  let : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (pullback.fst f j))
  let : Injective (M.restrict a) := inferInstance
  let : Injective ((moduleTensorLeftFunctor W
      ((Scheme.Modules.pullback b).obj (E.restrict j))).obj (M.restrict a)) :=
    tensor_pullback_affine_injective R b (E.restrict j) (M.restrict a)
  let : IsIso (cartesianPullbackBaseChangeMate a b f j
      (IsPullback.of_hasPullback f j)) :=
    cartesianPullbackBaseChangeMate_isIso a b f j (IsPullback.of_hasPullback f j)
  let e := ((SheafOfModulesOfCommRing.tensorFunctor W.sheaf).mapIso
    (asIso ((cartesianPullbackBaseChangeMate a b f j
      (IsPullback.of_hasPullback f j)).app E))).app (M.restrict a) ≪≫
    tensorRestrictionIso a ((Scheme.Modules.pullback f).obj E) M
  exact Injective.of_iso e
    (tensor_pullback_affine_injective R b (E.restrict j) (M.restrict a))
end AlgebraicGeometry.Scheme.Modules
