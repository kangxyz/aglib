/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension.FirstVariable
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Naturality
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Relative flatness of actual module sheaves

For `f : X ⟶ Y`, relative flatness means that the actual stalk of the coefficient
is flat over the base local ring through `f.stalkMap`. The original pullback
and tensor stalk comparisons then prove injective preservation for pullback
followed by tensoring with that coefficient. No quasicoherence, affineness or
flatness of `f` is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Flatness of the actual coefficient stalk over the actual base local ring. -/
def relativeFlat {X Y : Scheme.{u}} (f : X ⟶ Y) : ObjectProperty X.Modules :=
  fun M => ∀ x : X, Module.Flat (Y.presheaf.stalk (f x))
    ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj M))

/-- Ordinary pullback and tensor stalks, restricted to the original base local
ring, are the original base-stalk tensor with the restricted coefficient stalk. -/
def relativeTensorStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : X.Modules) :
    Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M ⋙ moduleStalk X x ⋙
        ModuleCat.restrictScalars (f.stalkMap x).hom ≅
      moduleStalk Y (f x) ⋙
        tensorRight ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((moduleStalk X x).obj M)) := by
  let e : moduleTensorRightFunctor X M ⋙ moduleStalk X x ≅
      moduleStalk X x ⋙ tensorRight ((moduleStalk X x).obj M) :=
    NatIso.ofComponents (fun N => moduleTensorStalkIso X x N M)
      (fun g => moduleTensorStalkIso_naturality_left X x g M)
  exact Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Functor.isoWhiskerRight e (ModuleCat.restrictScalars (f.stalkMap x).hom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (pullbackModuleStalkIso f x)
        (tensorRight ((moduleStalk X x).obj M)))
      (ModuleCat.restrictScalars (f.stalkMap x).hom) ≪≫
    Functor.isoWhiskerLeft (moduleStalk Y (f x))
      (ModuleCat.scalarExtensionTensorFirstVariableNatIso (f.stalkMap x).hom
        ((moduleStalk X x).obj M))

/-- Relative flatness preserves every actual monomorphism after ordinary
pullback and tensor-right by the original coefficient sheaf. -/
theorem mono_pullback_tensorRight_of_relativeFlat
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : X.Modules} (hM : relativeFlat f M)
    {N P : Y.Modules} (g : N ⟶ P) [Mono g] :
    Mono ((Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M).map g) := by
  apply mono_of_moduleStalk
  intro x
  let : Module.Flat (Y.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj M)) := hM x
  let e := relativeTensorStalkIso f x M
  have : Mono ((ModuleCat.restrictScalars (f.stalkMap x).hom).map
      ((moduleStalk X x).map
        ((Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M).map g)) ≫ e.hom.app P) := by
    change Mono
      (((Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M ⋙ moduleStalk X x ⋙
        ModuleCat.restrictScalars (f.stalkMap x).hom).map g) ≫ e.hom.app P)
    rw [e.hom.naturality]
    infer_instance
  have : Mono ((ModuleCat.restrictScalars (f.stalkMap x).hom).map
      ((moduleStalk X x).map
        ((Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M).map g))) :=
    mono_of_mono _ (e.hom.app P)
  exact (ModuleCat.restrictScalars (f.stalkMap x).hom).mono_of_mono_map inferInstance

/-- The actual pullback-tensor functor preserves monomorphisms under relative
flatness of its coefficient. -/
theorem pullback_tensorRight_preservesMonomorphisms_of_relativeFlat
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : X.Modules} (hM : relativeFlat f M) :
    (Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M).PreservesMonomorphisms where
  preserves g hg := by
    let := hg
    exact mono_pullback_tensorRight_of_relativeFlat f hM g

end AlgebraicGeometry.Scheme.Modules
