/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Canonical ideal comparisons for commutative squares

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/BaseChange.lean`, SHA-256
  `a5df3d28102fc6b3724618d2b1c94f913572db922d9f3ce48f6f9b1e2aa06faa`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}
variable {D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b)

/-- The canonical structure-module comparison induced by the displayed commutative square. -/
def squareStructureModuleMap :
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit D.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward b).obj
        ((Scheme.Modules.pushforward i').obj (SheafOfModules.unit D'.ringCatSheaf)) :=
  (Scheme.Modules.pushforward i).map (structureModuleMap a) ≫
    (Scheme.Modules.pushforwardComp a i).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr h).hom.app _ ≫
        (Scheme.Modules.pushforwardComp i' b).inv.app _

theorem squareStructureModuleMap_comm :
    structureModuleMap i ≫ squareStructureModuleMap i i' b a h =
      structureModuleMap b ≫ (Scheme.Modules.pushforward b).map (structureModuleMap i') := by
  calc
    _ = (structureModuleMap (a ≫ i) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app _) ≫
          (Scheme.Modules.pushforwardComp i' b).inv.app _ := by
      simp only [squareStructureModuleMap, structureModuleMap_comp, Category.assoc]
    _ = structureModuleMap (i' ≫ b) ≫ (Scheme.Modules.pushforwardComp i' b).inv.app _ := by
      rw [structureModuleMap_congr]
    _ = _ := by rw [structureModuleMap_comp]; simp

/-- The actual map of kernel modules induced by the commutative square and pushforward. -/
def idealPushforwardMap : idealModule i ⟶ (Scheme.Modules.pushforward b).obj (idealModule i') :=
  kernel.lift ((Scheme.Modules.pushforward b).map (structureModuleMap i'))
    (idealInclusion i ≫ structureModuleMap b)
    (by rw [Category.assoc, ← squareStructureModuleMap_comm i i' b a h,
      ← Category.assoc, idealInclusion_structureMap, Limits.zero_comp]) ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward b) (structureModuleMap i')).inv

@[reassoc (attr := simp)]
theorem idealPushforwardMap_inclusion :
    idealPushforwardMap i i' b a h ≫
      (Scheme.Modules.pushforward b).map (idealInclusion i') =
        idealInclusion i ≫ structureModuleMap b := by
  simp only [idealPushforwardMap, idealInclusion, Category.assoc, PreservesKernel.iso_inv_ι,
    kernel.lift_ι]

/-- The canonical ideal comparison adjoint to the actual pushforward kernel map. -/
def idealPullbackMap : (Scheme.Modules.pullback b).obj (idealModule i) ⟶ idealModule i' :=
  ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).symm
    (idealPushforwardMap i i' b a h)

@[simp]
theorem idealPullbackMap_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _ (idealPullbackMap i i' b a h) =
      idealPushforwardMap i i' b a h := Equiv.apply_symm_apply _ _

theorem idealPullbackMap_inclusion : idealPullbackMap i i' b a h ≫ idealInclusion i' =
    (Scheme.Modules.pullback b).map (idealInclusion i) ≫
      SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, idealPullbackMap_adjoint,
    idealPushforwardMap_inclusion, Adjunction.homEquiv_naturality_left]
  congr 1
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    b.toRingCatSheafHom).symm

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X₀ X₁ X₂ D₀ D₁ D₂ : Scheme.{u}}
variable (i₀ : D₀ ⟶ X₀) (i₁ : D₁ ⟶ X₁) (i₂ : D₂ ⟶ X₂)
variable (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁) (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁)
variable (h₁ : a₁ ≫ i₀ = i₁ ≫ b₁) (h₂ : a₂ ≫ i₁ = i₂ ≫ b₂)

theorem idealPushforwardMap_comp :
    idealPushforwardMap i₀ i₂ (b₂ ≫ b₁) (a₂ ≫ a₁)
      (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) =
    idealPushforwardMap i₀ i₁ b₁ a₁ h₁ ≫
      (Scheme.Modules.pushforward b₁).map (idealPushforwardMap i₁ i₂ b₂ a₂ h₂) ≫
      (Scheme.Modules.pushforwardComp b₂ b₁).hom.app (idealModule i₂) := by
  apply (cancel_mono ((Scheme.Modules.pushforward (b₂ ≫ b₁)).map (idealInclusion i₂))).mp
  rw [idealPushforwardMap_inclusion]
  rw [Category.assoc, Category.assoc,
    ← (Scheme.Modules.pushforwardComp b₂ b₁).hom.naturality (idealInclusion i₂)]
  simp only [Functor.comp_map]
  rw [← Category.assoc ((Scheme.Modules.pushforward b₁).map
      (idealPushforwardMap i₁ i₂ b₂ a₂ h₂)), ← Functor.map_comp,
    idealPushforwardMap_inclusion, Functor.map_comp]
  simp only [← Category.assoc, idealPushforwardMap_inclusion]
  rw [structureModuleMap_comp]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Modules

variable {X₀ X₁ X₂ D₀ D₁ D₂ : Scheme.{u}}
variable (i₀ : D₀ ⟶ X₀) (i₁ : D₁ ⟶ X₁) (i₂ : D₂ ⟶ X₂)
variable (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁) (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁)
variable (h₁ : a₁ ≫ i₀ = i₁ ≫ b₁) (h₂ : a₂ ≫ i₁ = i₂ ≫ b₂)

private theorem pullbackComp_homEquiv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (φ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
      ((Scheme.Modules.pullbackComp f g).inv.app M ≫ φ) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv M N φ ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  let adj₁ := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let adj₂ := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have h : adj₂.homEquiv M N ((Scheme.Modules.pullbackComp f g).inv.app M ≫ φ) =
      adj₁.homEquiv M N φ ≫
        (conjugateEquiv adj₁ adj₂ (Scheme.Modules.pullbackComp f g).inv).app N := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc,
      ← unit_conjugateEquiv adj₁ adj₂ (Scheme.Modules.pullbackComp f g).inv M, Category.assoc]
    simpa only [Functor.comp_obj, Category.assoc] using
      congrArg (fun ψ ↦ adj₁.unit.app M ≫ ψ)
        ((conjugateEquiv adj₁ adj₂ (Scheme.Modules.pullbackComp f g).inv).naturality φ).symm
  simpa only [adj₁, adj₂, Scheme.Modules.conjugateEquiv_pullbackComp_inv] using h

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X₀ X₁ X₂ D₀ D₁ D₂ : Scheme.{u}}
variable (i₀ : D₀ ⟶ X₀) (i₁ : D₁ ⟶ X₁) (i₂ : D₂ ⟶ X₂)
variable (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁) (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁)
variable (h₁ : a₁ ≫ i₀ = i₁ ≫ b₁) (h₂ : a₂ ≫ i₁ = i₂ ≫ b₂)

/-- The canonical ideal comparison commutes with composition of its actual squares. -/
theorem idealPullbackMap_comp :
    (Scheme.Modules.pullbackComp b₂ b₁).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback b₂).map (idealPullbackMap i₀ i₁ b₁ a₁ h₁) ≫
      idealPullbackMap i₁ i₂ b₂ a₂ h₂ =
    idealPullbackMap i₀ i₂ (b₂ ≫ b₁) (a₂ ≫ a₁)
      (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (b₂ ≫ b₁)).homEquiv _ _).injective
  rw [pullbackComp_homEquiv, idealPullbackMap_adjoint, Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction b₁).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction b₂).homEquiv _ _
      ((Scheme.Modules.pullback b₂).map (idealPullbackMap i₀ i₁ b₁ a₁ h₁) ≫
        idealPullbackMap i₁ i₂ b₂ a₂ h₂)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    idealPullbackMap_adjoint, idealPullbackMap_adjoint]
  exact (idealPushforwardMap_comp i₀ i₁ i₂ b₁ b₂ a₁ a₂ h₁ h₂).symm

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {D X Y : Scheme.{u}}
variable {D' : Scheme.{u}}

theorem idealPullbackMap_eq_of_same_base (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a a' : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (h' : a' ≫ i = i' ≫ b) :
    idealPullbackMap i i' b a h = idealPullbackMap i i' b a' h' := by
  apply (cancel_mono (idealInclusion i')).mp
  rw [idealPullbackMap_inclusion, idealPullbackMap_inclusion]

theorem idealPullbackMap_isIso_of_eq_base (i : D ⟶ X) (i' : D' ⟶ Y)
    (b b' : Y ⟶ X) (a a' : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (h' : a' ≫ i = i' ≫ b') (hb : b = b')
    [IsIso (idealPullbackMap i i' b' a' h')] :
    IsIso (idealPullbackMap i i' b a h) := by
  subst b'
  rw [idealPullbackMap_eq_of_same_base i i' b a a' h h']
  infer_instance

end AlgebraicGeometry.Scheme.Hom
end
