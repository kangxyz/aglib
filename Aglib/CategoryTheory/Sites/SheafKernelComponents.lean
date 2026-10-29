/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual sheaf kernels from component lifts

An injective actual inclusion and actual lifts of its kernel sections construct
the complete additive, natural sheaf lift and the universal property of that
same fork. No replacement kernel object or sheafification model is selected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {L M N : Sheaf J AddCommGrpCat.{w}}

/-- Injectivity of the original component maps proves monicity of the same sheaf map. -/
theorem mono_of_component_injective (i : L ⟶ M)
    (hi : ∀ U, Function.Injective (i.hom.app U)) : Mono i where
  right_cancellation a b h := by
    ext U x
    apply hi U
    exact ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) h) x

/-- An actual zero composite annihilates every original component value. -/
theorem componentKernel_condition (p : M ⟶ N) {P : Sheaf J AddCommGrpCat.{w}}
    (φ : P ⟶ M) (h : φ ≫ p = 0) (U : Cᵒᵖ) (a : P.obj.obj U) :
    p.hom.app U (φ.hom.app U a) = 0 :=
  ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) h) a

variable (i : L ⟶ M) (p : M ⟶ N)
variable (hi : ∀ U, Function.Injective (i.hom.app U))
variable (s : ∀ U (a : M.obj.obj U), p.hom.app U a = 0 → L.obj.obj U)
variable (hs : ∀ U (a : M.obj.obj U) (h : p.hom.app U a = 0), i.hom.app U (s U a h) = a)

/-- Actual component lifts assemble into the complete additive and natural sheaf lift. -/
def componentKernelLift {P : Sheaf J AddCommGrpCat.{w}}
    (φ : P ⟶ M) (h : φ ≫ p = 0) : P ⟶ L where
  hom := {
    app U := AddCommGrpCat.ofHom {
      toFun a := s U (φ.hom.app U a) (componentKernel_condition p φ h U a)
      map_zero' := by
        apply hi U
        rw [hs, map_zero, map_zero]
      map_add' a b := by
        apply hi U
        rw [hs, map_add, map_add, hs, hs] }
    naturality {U V} f := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      apply hi V
      change i.hom.app V (s V (φ.hom.app V (P.obj.map f a))
          (componentKernel_condition p φ h V (P.obj.map f a))) =
        i.hom.app V (L.obj.map f (s U (φ.hom.app U a) (componentKernel_condition p φ h U a)))
      have hn := ConcreteCategory.congr_hom (i.hom.naturality f)
        (s U (φ.hom.app U a) (componentKernel_condition p φ h U a))
      change i.hom.app V (L.obj.map f (s U (φ.hom.app U a)
          (componentKernel_condition p φ h U a))) =
        M.obj.map f (i.hom.app U (s U (φ.hom.app U a)
          (componentKernel_condition p φ h U a))) at hn
      rw [hs, hn, hs]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) a }

/-- The assembled lift keeps the supplied original section lift as its literal value. -/
@[simp] theorem componentKernelLift_apply {P : Sheaf J AddCommGrpCat.{w}}
    (φ : P ⟶ M) (h : φ ≫ p = 0) (U : Cᵒᵖ) (a : P.obj.obj U) :
    (componentKernelLift i p hi s hs φ h).hom.app U a =
      s U (φ.hom.app U a) (componentKernel_condition p φ h U a) := rfl

/-- The whole lifted sheaf map factors the original map through the actual inclusion. -/
@[simp] theorem componentKernelLift_fac {P : Sheaf J AddCommGrpCat.{w}}
    (φ : P ⟶ M) (h : φ ≫ p = 0) : componentKernelLift i p hi s hs φ h ≫ i = φ := by
  ext U a
  exact hs U (φ.hom.app U a) (componentKernel_condition p φ h U a)

/-- The supplied actual component lifts prove the kernel universal property on the same fork. -/
def componentKernelIsLimit (h : i ≫ p = 0) : IsLimit (KernelFork.ofι i h) := by
  letI := mono_of_component_injective i hi
  exact KernelFork.IsLimit.ofι' i h (fun φ hφ =>
    ⟨componentKernelLift i p hi s hs φ hφ, componentKernelLift_fac i p hi s hs φ hφ⟩)

/-- The actual kernel of an actual multiplication map is annihilated by its integer. -/
theorem componentKernel_nsmul_id_eq_zero (n : ℕ) (j : L ⟶ M)
    (hj : ∀ U, Function.Injective (j.hom.app U)) (q : M ⟶ M) (hjq : j ≫ q = 0)
    (hq : ∀ U (a : M.obj.obj U), q.hom.app U a = n • a) : n • (𝟙 L) = 0 := by
  ext U a
  apply hj U
  change j.hom.app U (n • a) = j.hom.app U 0
  rw [map_nsmul, map_zero, ← hq]
  exact componentKernel_condition q j hjq U a

end CategoryTheory.Sheaf
