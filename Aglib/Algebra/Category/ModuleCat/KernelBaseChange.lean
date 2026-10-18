/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Scalar extension of actual ring-kernel maps

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits Opposite
open TensorProduct
open LinearMap

section
namespace ModuleCat

variable {R : CommRingCat.{u}} {M N : ModuleCat R}

/-- The given ring homomorphism as a map to the scalar-restricted unit module. -/
def ringHomModuleMap {S : CommRingCat.{u}} (φ : R ⟶ S) :
    ModuleCat.of R R ⟶ (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) :=
  ModuleCat.ofHom (X := ModuleCat.of R R)
    (Y := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
    { toFun := φ
      map_add' := map_add φ.hom
      map_smul' := fun r s ↦ map_mul φ.hom r s }

end ModuleCat
end

section
namespace ModuleCat

variable {R : CommRingCat.{u}}

/-- The actual unit-to-unit scalar-extension map adjoint to the given ring map. -/
def scalarExtensionUnit {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R R) ⟶ ModuleCat.of S S :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    (ModuleCat.ringHomModuleMap φ)

/-- The map between actual ring-kernel modules induced by the commutative square. -/
def kernelMap {S R' S' : CommRingCat.{u}} (φ : R ⟶ S) (φ' : R' ⟶ S')
    (b : R ⟶ R') (a : S ⟶ S') (h : φ ≫ a = b ≫ φ') :
    ModuleCat.of R (RingHom.ker φ.hom) ⟶
      (ModuleCat.restrictScalars b.hom).obj (ModuleCat.of R' (RingHom.ker φ'.hom)) :=
  ModuleCat.ofHom (X := ModuleCat.of R (RingHom.ker φ.hom))
    (Y := (ModuleCat.restrictScalars b.hom).obj (ModuleCat.of R' (RingHom.ker φ'.hom)))
    { toFun := fun x ↦ ⟨b x, by
        change φ'.hom (b.hom x) = 0
        have hx := congrArg (fun k : R ⟶ S' ↦ k x) h
        change a.hom (φ.hom x) = φ'.hom (b.hom x) at hx
        rw [← hx, x.property, map_zero]⟩
      map_add' := fun x y ↦ Subtype.ext (map_add b.hom (x : R) (y : R))
      map_smul' := fun r x ↦ Subtype.ext (map_mul b.hom r (x : R)) }

/-- The adjoint scalar-extension map between the actual ring kernels. -/
def extendedKernelMap {S R' S' : CommRingCat.{u}} (φ : R ⟶ S) (φ' : R' ⟶ S')
    (b : R ⟶ R') (a : S ⟶ S') (h : φ ≫ a = b ≫ φ') :
    (ModuleCat.extendScalars b.hom).obj (ModuleCat.of R (RingHom.ker φ.hom)) ⟶
      ModuleCat.of R' (RingHom.ker φ'.hom) :=
  ((ModuleCat.extendRestrictScalarsAdj b.hom).homEquiv _ _).symm
    (ModuleCat.kernelMap φ φ' b a h)

@[reassoc]
theorem extendedKernelMap_inclusion {S R' S' : CommRingCat.{u}}
    (φ : R ⟶ S) (φ' : R' ⟶ S') (b : R ⟶ R') (a : S ⟶ S')
    (h : φ ≫ a = b ≫ φ') :
    ModuleCat.extendedKernelMap φ φ' b a h ≫ ModuleCat.ofHom (RingHom.ker φ'.hom).subtype =
      (ModuleCat.extendScalars b.hom).map (ModuleCat.ofHom (RingHom.ker φ.hom).subtype) ≫
        ModuleCat.scalarExtensionUnit b := by
  apply (ModuleCat.extendRestrictScalarsAdj b.hom).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  simp only [ModuleCat.extendedKernelMap, ModuleCat.scalarExtensionUnit, Equiv.apply_symm_apply]
  rfl

end ModuleCat
end

section
namespace ModuleCat

open scoped ChangeOfRings

/-- The comparison from categorical scalar extension to the native tensor
product is natural for the actual scalar-extended linear map. -/
theorem extendScalarsAlgebraIso_naturality (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R T)).map φ ≫
      (ModuleCat.extendScalarsAlgebraIso R T N).hom =
    (ModuleCat.extendScalarsAlgebraIso R T M).hom ≫
      ModuleCat.ofHom (φ.hom.baseChange T) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (ModuleCat.extendScalarsAlgebraIso R T N).hom
      ((ModuleCat.extendScalars (algebraMap R T)).map φ ((1 : T) ⊗ₜ[R,algebraMap R T] m)) =
    (φ.hom.baseChange T) ((ModuleCat.extendScalarsAlgebraIso R T M).hom ((1 : T) ⊗ₜ[R,algebraMap R
      T] m))
  rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.extendScalarsAlgebraIso_tmul,
    ModuleCat.extendScalarsAlgebraIso_tmul]
  rfl

end ModuleCat
end
