/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Biproduct
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Open
public import Aglib.RingTheory.Length.ScalarFactorization

/-!
# Original scalar factorizations on structural cohomology

An actual coefficient-map factorization through global scalar multiplication
induces the same factorization on original structural cohomology. Its kernel
and the native finite-biproduct comparison give the corresponding length
bound. Scalar restriction uses the original global coefficient map, with no
new action or replacement cohomology object. The current consumer is the
finite trace-coordinate bound for surface modifications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original composed scalar map gives the actual scalar tower on
unchanged cohomology. -/
abbrev moduleCohomologyScalarTower (X : Scheme.{u})
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (β : B →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X β M n
    letI := moduleCohomologyModuleOfHom X (β.comp (algebraMap A B)) M n
    IsScalarTower A B (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) := by
  let := moduleCohomologyModuleOfHom X β M n
  let := moduleCohomologyModuleOfHom X (β.comp (algebraMap A B)) M n
  refine ⟨?_⟩
  intro a b x
  change (moduleCohomologyGlobalScalars X M n) (β (a • b)) x =
    (moduleCohomologyGlobalScalars X M n) (β (algebraMap A B a))
      ((moduleCohomologyGlobalScalars X M n) (β b) x)
  rw [Algebra.smul_def, β.map_mul, (moduleCohomologyGlobalScalars X M n).map_mul]
  rfl

/-- An actual equality of original global scalar maps identifies the
structural actions in the same scalar tower. -/
abbrev moduleCohomologyScalarTowerOfEq (X : Scheme.{u})
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(X, ⊤))
    (h : α = β.comp (algebraMap A B)) (M : X.Modules) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X β M n
    letI := moduleCohomologyModuleOfHom X α M n
    IsScalarTower A B (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) := by
  subst α
  exact moduleCohomologyScalarTower X A B β M n

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) {M N : X.Modules}

/-- The original sheaf coefficient maps retain their scalar factorization
on original cohomology, with the specified structural action. -/
theorem moduleCohomologyMap_scalarFactorization (d : R)
    (φ : M ⟶ N) (ψ : N ⟶ M)
    (h : φ ≫ ψ = globalScalarEndomorphism X M (α d)) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    (moduleCohomologyMapOfHom X α ψ n).comp
        (moduleCohomologyMapOfHom X α φ n) = d • LinearMap.id := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom X α N n
  let F := moduleCohomologyFunctorOfHom X α n
  have he : F.map φ ≫ F.map ψ = F.map (globalScalarEndomorphism X M (α d)) :=
    (F.map_comp φ ψ).symm.trans (congrArg F.map h)
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) x
  change (moduleCohomologyMapOfHom X α ψ n)
      ((moduleCohomologyMapOfHom X α φ n) x) = _ at hx
  refine hx.trans ?_
  change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
    (globalScalarEndomorphism X M (α d))) n x = d • x
  rw [moduleGlobalScalar_toAddSheaf]
  rfl

/-- Length of the original coefficient source is bounded by its original
scalar torsion and the actual coefficient target. -/
theorem moduleCohomology_length_le_of_scalarFactorization (d : R)
    (φ : M ⟶ N) (ψ : N ⟶ M)
    (h : φ ≫ ψ = globalScalarEndomorphism X M (α d)) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    Module.length R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) ≤
      Module.length R
          (Submodule.torsionBy R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) d) +
        Module.length R (Sheaf.H.{u + 1} (moduleAddSheaf X N) n) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom X α N n
  exact Module.length_le_torsionBy_add_of_comp_smul_id d
    (moduleCohomologyMapOfHom X α φ n) (moduleCohomologyMapOfHom X α ψ n)
    (moduleCohomologyMap_scalarFactorization X α d φ ψ h n)

end AlgebraicGeometry.Scheme.Cohomology
