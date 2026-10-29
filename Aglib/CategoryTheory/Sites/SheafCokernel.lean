/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Restriction of represented sections in sheaf cokernels

The cokernel class of a section restricts to zero along a site arrow when the
restricted section has a supplied lift through the original sheaf morphism.
Only the cokernel of that morphism is required.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A represented sheaf-cokernel section restricts to zero wherever it has a supplied lift. -/
theorem cokernel_restriction_zero {A B : Sheaf J AddCommGrpCat.{w}} (φ : A ⟶ B)
    [HasCokernel φ] {U V : C} (f : V ⟶ U)
    (a : B.obj.obj (op U)) (b : A.obj.obj (op V))
    (h : φ.hom.app (op V) b = B.obj.map f.op a) :
    (cokernel φ).obj.map f.op ((cokernel.π φ).hom.app (op U) a) = 0 := by
  have hn := ConcreteCategory.congr_hom ((cokernel.π φ).hom.naturality f.op) a
  have hz := congrArg (fun k : A ⟶ cokernel φ => k.hom.app (op V)) (cokernel.condition φ)
  have hzv := ConcreteCategory.congr_hom hz b
  change (cokernel.π φ).hom.app (op V) (φ.hom.app (op V) b) = 0 at hzv
  exact hn.symm.trans ((congrArg (fun c => (cokernel.π φ).hom.app (op V) c) h.symm).trans hzv)

end CategoryTheory.Sheaf
