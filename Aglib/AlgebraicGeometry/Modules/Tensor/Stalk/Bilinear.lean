/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Pure

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorStalkBilinear.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 142]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Bilinearity of the original tensor on module germs
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry TopologicalSpace Opposite SheafOfModulesOfCommRing

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Three module germs have representatives over one open neighborhood. -/
theorem exists_three_module_germ_representatives (X : Scheme.{u}) (x : X)
    (M N P : X.Modules) (m : M.presheaf.stalk x) (n : N.presheaf.stalk x)
    (p : P.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) (v : Γ(P, U)),
      M.presheaf.germ U x hx s = m ∧ N.presheaf.germ U x hx t = n ∧
        P.presheaf.germ U x hx v = p := by
  obtain ⟨V, hxV, s, t, rfl, rfl⟩ := exists_two_module_germ_representatives X x M N m n
  obtain ⟨U, hUV, hxU, v, rfl⟩ := P.presheaf.exists_le_germ_eq p hxV
  exact ⟨U, hxU, M.presheaf.map (homOfLE hUV).op s,
    N.presheaf.map (homOfLE hUV).op t, v, M.presheaf.germ_res_apply _ _ _ _,
    N.presheaf.germ_res_apply _ _ _ _, rfl⟩

/-- A scalar and two module germs have common representatives. -/
theorem exists_scalar_two_module_germ_representatives (X : Scheme.{u}) (x : X)
    (M N : X.Modules) (r : X.presheaf.stalk x)
    (m : M.presheaf.stalk x) (n : N.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)),
      X.presheaf.germ U x hx a = r ∧ M.presheaf.germ U x hx s = m ∧
        N.presheaf.germ U x hx t = n := by
  obtain ⟨V, hxV, a, s, rfl, rfl⟩ := exists_germ_smul_representatives X x M r m
  obtain ⟨U, hUV, hxU, t, rfl⟩ := N.presheaf.exists_le_germ_eq n hxV
  exact ⟨U, hxU, X.presheaf.map (homOfLE hUV).op a,
    M.presheaf.map (homOfLE hUV).op s, t, X.presheaf.germ_res_apply _ _ _ _,
    M.presheaf.germ_res_apply _ _ _ _, rfl⟩

/-- The original module-sheafification unit on the sectionwise tensor. -/
def moduleTensorSectionLinear (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens) :
    TensorProduct Γ(X, U) Γ(M, U) Γ(N, U) →ₗ[Γ(X, U)]
      Γ((moduleTensorLeftFunctor X M).obj N, U) :=
  (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app (M.val ⊗ N.val)).app (op U)).hom

theorem moduleTensorSection_add_left (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (s s' : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorSection X M N U (s + s') t =
      moduleTensorSection X M N U s t + moduleTensorSection X M N U s' t := by
  change moduleTensorSectionLinear X M N U ((s + s') ⊗ₜ t) =
    moduleTensorSectionLinear X M N U (s ⊗ₜ t) +
      moduleTensorSectionLinear X M N U (s' ⊗ₜ t)
  rw [TensorProduct.add_tmul, map_add]

theorem moduleTensorSection_add_right (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t t' : Γ(N, U)) :
    moduleTensorSection X M N U s (t + t') =
      moduleTensorSection X M N U s t + moduleTensorSection X M N U s t' := by
  change moduleTensorSectionLinear X M N U (s ⊗ₜ (t + t')) =
    moduleTensorSectionLinear X M N U (s ⊗ₜ t) +
      moduleTensorSectionLinear X M N U (s ⊗ₜ t')
  rw [TensorProduct.tmul_add, map_add]

theorem moduleTensorSection_smul_left (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorSection X M N U (a • s) t = a • moduleTensorSection X M N U s t := by
  change moduleTensorSectionLinear X M N U ((a • s) ⊗ₜ t) =
    a • moduleTensorSectionLinear X M N U (s ⊗ₜ t)
  rw [← TensorProduct.smul_tmul', _root_.map_smul]

theorem moduleTensorSection_smul_right (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorSection X M N U s (a • t) = a • moduleTensorSection X M N U s t := by
  change moduleTensorSectionLinear X M N U (s ⊗ₜ (a • t)) =
    a • moduleTensorSectionLinear X M N U (s ⊗ₜ t)
  rw [TensorProduct.tmul_smul, _root_.map_smul]

theorem moduleTensorStalkPure_add_left (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (m m' : M.presheaf.stalk x) (n : N.presheaf.stalk x) :
    moduleTensorStalkPure X x M N (m + m') n =
      moduleTensorStalkPure X x M N m n + moduleTensorStalkPure X x M N m' n := by
  obtain ⟨U, hx, s, s', t, rfl, rfl, rfl⟩ :=
    exists_three_module_germ_representatives X x M M N m m' n
  rw [← map_add, moduleTensorStalkPure_germ, moduleTensorStalkPure_germ,
    moduleTensorStalkPure_germ, moduleTensorSection_add_left, map_add]

theorem moduleTensorStalkPure_add_right (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (m : M.presheaf.stalk x) (n n' : N.presheaf.stalk x) :
    moduleTensorStalkPure X x M N m (n + n') =
      moduleTensorStalkPure X x M N m n + moduleTensorStalkPure X x M N m n' := by
  obtain ⟨U, hx, s, t, t', rfl, rfl, rfl⟩ :=
    exists_three_module_germ_representatives X x M N N m n n'
  rw [← map_add, moduleTensorStalkPure_germ, moduleTensorStalkPure_germ,
    moduleTensorStalkPure_germ, moduleTensorSection_add_right, map_add]

theorem moduleTensorStalkPure_smul_left (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) (n : N.presheaf.stalk x) :
    moduleTensorStalkPure X x M N (r • m) n = r • moduleTensorStalkPure X x M N m n := by
  obtain ⟨U, hx, a, s, t, rfl, rfl, rfl⟩ :=
    exists_scalar_two_module_germ_representatives X x M N r m n
  erw [← PresheafOfModules.germ_smul M.val x U hx,
    moduleTensorStalkPure_germ, moduleTensorStalkPure_germ, moduleTensorSection_smul_left,
    PresheafOfModules.germ_smul ((moduleTensorLeftFunctor X M).obj N).val x U hx]
  rfl

theorem moduleTensorStalkPure_smul_right (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) (n : N.presheaf.stalk x) :
    moduleTensorStalkPure X x M N m (r • n) = r • moduleTensorStalkPure X x M N m n := by
  obtain ⟨U, hx, a, s, t, rfl, rfl, rfl⟩ :=
    exists_scalar_two_module_germ_representatives X x M N r m n
  erw [← PresheafOfModules.germ_smul N.val x U hx,
    moduleTensorStalkPure_germ, moduleTensorStalkPure_germ, moduleTensorSection_smul_right,
    PresheafOfModules.germ_smul ((moduleTensorLeftFunctor X M).obj N).val x U hx]
  rfl

/-- The canonical linear map from the tensor of the original module stalks. -/
def moduleTensorStalkInv (X : Scheme.{u}) (x : X) (M N : X.Modules) :
    (moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N ⟶
      (moduleStalk X x).obj ((moduleTensorLeftFunctor X M).obj N) :=
  ModuleCat.MonoidalCategory.tensorLift (moduleTensorStalkPure X x M N)
    (moduleTensorStalkPure_add_left X x M N) (moduleTensorStalkPure_smul_left X x M N)
    (moduleTensorStalkPure_add_right X x M N) (moduleTensorStalkPure_smul_right X x M N)

/-- The inverse candidate retains the original pure-tensor germ formula. -/
theorem moduleTensorStalkInv_tmul_germ (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorStalkInv X x M N
        (M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t) =
      ((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
        (moduleTensorSection X M N U s t) :=
  moduleTensorStalkPure_germ X x M N U hx s t

end AlgebraicGeometry.Scheme.Modules
