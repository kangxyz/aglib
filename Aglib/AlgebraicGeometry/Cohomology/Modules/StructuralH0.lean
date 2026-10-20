/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Structural H0 and section cokernels

For an arbitrary scheme over a field, the original Ext-defined H0 is
identified linearly with its actual structural sections. Naturality
preserves the original coefficient map and its cokernel, allowing finite
native-section cokernels to give finite H0 cokernels. No curve, properness,
or finite-type hypothesis occurs.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurves.ProjectiveLine`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing declaration
namespaces, hypotheses, universes, objects, maps, and proofs are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Modules.StructuralH0` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e79c9d3673108ad155d0e44e37a047c958d64c7cb92cf1c32309ae485463e724`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
universe u v
namespace AlgebraicGeometry.Scheme.Cohomology
variable {K : Type u} [Field K] (X : FScheme K)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (moduleCohomology moduleCohomologyMap moduleH0Equiv coefficientSheafMap)
/-- Identity on sections, with the actual structural field action on both sides. -/
def structuralSectionsIso (M : X.left.Modules) :
    ModuleCat.of K (M.val.obj (op ⊤)) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward X.hom).obj M) := by
  let e : M.val.obj (op ⊤) ≃ₗ[K]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward X.hom).obj M) := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by intro a x; rfl }
  exact e.toModuleIso

/-- Actual Ext-defined H0 identifies linearly with native structural sections. -/
def structuralH0Equiv (M : X.left.Modules) :
    moduleCohomology K X M 0 ≃ₗ[K]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward X.hom).obj M) :=
  (moduleH0Equiv X M).trans (structuralSectionsIso X M).toLinearEquiv

/-- The H0 comparison preserves the original coefficient map. -/
theorem structuralH0Equiv_naturality {M N : X.left.Modules} (φ : M ⟶ N)
    (x : moduleCohomology K X M 0) :
    structuralH0Equiv X N (moduleCohomologyMap X φ 0 x) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward X.hom).map φ)
        (structuralH0Equiv X M x) := by
  exact (Sheaf.H.equiv₀_naturality isTerminalTop (coefficientSheafMap X φ) x).symm

/-- The corresponding actual H0 and native-section cokernels agree linearly. -/
def structuralH0CokernelEquiv {M N : X.left.Modules} (φ : M ⟶ N) :
    (moduleCohomology K X N 0 ⧸ LinearMap.range (moduleCohomologyMap X φ 0)) ≃ₗ[K]
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward X.hom).obj N) ⧸
        LinearMap.range (moduleSpecΓFunctor.map
          ((Scheme.Modules.pushforward X.hom).map φ)).hom) := by
  apply Submodule.Quotient.equiv _ _ (structuralH0Equiv X N)
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨structuralH0Equiv X M x, (structuralH0Equiv_naturality X φ x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨moduleCohomologyMap X φ 0 ((structuralH0Equiv X M).symm x), ⟨_, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe, structuralH0Equiv_naturality,
      LinearEquiv.apply_symm_apply]

/-- Transfer finite native-section cokernels to the original H0 objects. -/
theorem structuralH0Cokernel_finite {M N : X.left.Modules} (φ : M ⟶ N)
    [Module.Finite K (↑(cokernel (moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward X.hom).map φ)) : ModuleCat.{u} K))] :
    Module.Finite K (moduleCohomology K X N 0 ⧸
      LinearMap.range (moduleCohomologyMap X φ 0)) := by
  have : Module.Finite K
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward X.hom).obj N) ⧸
        LinearMap.range (moduleSpecΓFunctor.map
          ((Scheme.Modules.pushforward X.hom).map φ)).hom) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv
  exact Module.Finite.equiv (structuralH0CokernelEquiv X φ).symm


end AlgebraicGeometry.Scheme.Cohomology
