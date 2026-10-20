/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Compatibility with the explicit tensor-pullback theorem family

The incoming R5 `Modules/Invertible/PullbackTensor/{Properties,Isomorphism}`
interface at revision `f8a3314ddecffcada2ec721d26d56a937bed9690` is supplied
by the native theorem on the same canonical map. The line-bundle and Picard
comparisons below delegate to the native implementation. All schemes and
module sheaves are allowed; the explicit family parameter is retained only
for compatibility with incoming consumers.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u

/-- The original theorem-family interface on the actual canonical tensor map. -/
def ModuleTensorPullback : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M N : Y.Modules),
    IsIso (pullbackTensorMap f M N)

/-- The native bilinear-adjunction proof supplies the original interface. -/
theorem moduleTensorPullback : ModuleTensorPullback.{u} :=
  fun _ _ f M N ↦ Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso f M N

variable {X Y : Scheme.{u}}

/-- The isomorphism whose forward arrow is the canonical tensor-pullback map. -/
def pullbackTensorIso (_h : ModuleTensorPullback.{u}) (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensorSheaf Y M N) ≅
      (show X.Modules from tensorSheaf X ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) := by
  haveI := moduleTensorPullback X Y f M N
  exact asIso (pullbackTensorMap f M N)

@[simp] theorem pullbackTensorIso_hom (h : ModuleTensorPullback.{u})
    (f : X ⟶ Y) (M N : Y.Modules) :
    (pullbackTensorIso h f M N).hom = pullbackTensorMap f M N := rfl

abbrev pullbackLineBundleTensorIso (_h : ModuleTensorPullback.{u})
    (f : X ⟶ Y) (L M : LineBundle Y) :=
  PullbackTensor.Local.pullbackLineBundleTensorIso f L M

theorem pullbackClass_add (_h : ModuleTensorPullback.{u}) (f : X ⟶ Y)
    (a b : PicardGroup Y) : pullbackClass f (a + b) = pullbackClass f a + pullbackClass f b :=
  PullbackTensor.Local.pullbackClass_add f a b

abbrev pullbackHom (_h : ModuleTensorPullback.{u}) (f : X ⟶ Y) :=
  PullbackTensor.Local.pullbackHom f

@[simp] theorem pullbackHom_apply (h : ModuleTensorPullback.{u}) (f : X ⟶ Y)
    (a : PicardGroup Y) : pullbackHom h f a = pullbackClass f a := rfl

theorem pullbackClass_neg (_h : ModuleTensorPullback.{u}) (f : X ⟶ Y)
    (a : PicardGroup Y) : pullbackClass f (-a) = -pullbackClass f a :=
  PullbackTensor.Local.pullbackClass_neg f a

@[simp] theorem pullbackHom_id (h : ModuleTensorPullback.{u}) :
    pullbackHom h (𝟙 X) = AddMonoidHom.id (PicardGroup X) := by
  ext a
  exact pullbackClass_id a

@[simp] theorem pullbackHom_comp (h : ModuleTensorPullback.{u})
    {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackHom h (f ≫ g) = (pullbackHom h f).comp (pullbackHom h g) := by
  ext a
  exact pullbackClass_comp f g a

end AlgebraicGeometry.Scheme.Modules.Invertible
