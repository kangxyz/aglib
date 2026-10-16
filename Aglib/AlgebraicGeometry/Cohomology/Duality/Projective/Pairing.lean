/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear

/-!
# The original projective Yoneda and Serre pairings

Native module-linear Yoneda composition, the unchanged module-Ext/cohomology comparison,
and the proved geometric trace define the canonical pairing. In Ext degree zero it is
exactly trace after the original coefficient cohomology map. No perfectness hypothesis
or replacement pairing is used in these definitions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- Native module Yoneda composition followed by the original geometric trace. -/
def projectiveYonedaPairing (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (i j : ℕ) (hij : i + j = n) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) j →ₗ[R]
      Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) M i →ₗ[R] R := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let O : (ProjectiveSpace R ι).Modules :=
    SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α ω n
  exact (Ext.bilinearCompOfLinear R O M ω i j n hij).flip.compr₂
    ((projectiveTrace R ι n e).comp
      (moduleExtCohomologyLinearEquivOfCategory (ProjectiveSpace R ι) α ω n).toLinearMap)

/-- The canonical Serre pairing uses the original actual cohomology in its second input. -/
def projectiveSerrePairing (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (i j : ℕ) (hij : i + j = n) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M i
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) j →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) i →ₗ[R] R := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M i
  exact (projectiveYonedaPairing R ι n e M i j hij).compl₂
    (moduleExtCohomologyLinearEquivOfCategory (ProjectiveSpace R ι) α M i).symm.toLinearMap

/-- The pairing retains literal native Yoneda composition and the original comparison. -/
theorem projectiveSerrePairing_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (i j : ℕ) (hij : i + j = n)
    (y : Ext.{u + 1} M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) j)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) i) :
    projectiveSerrePairing R ι n e M i j hij y x =
      projectiveTrace R ι n e (moduleExtCohomologyMap (ProjectiveSpace R ι)
        (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
          (((moduleExtCohomologyAddEquiv (ProjectiveSpace R ι) M i).symm x).comp y hij)) := rfl

/-- In native Ext degree zero, the pairing is exactly trace after the original actual
coefficient cohomology map. -/
theorem projectiveSerrePairing_mk₀ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (f : M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
    projectiveSerrePairing R ι n e M n 0 (Nat.add_zero n) (Ext.mk₀ f) x =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x) := by
  rw [projectiveSerrePairing_apply, moduleExtCohomologyMap_naturality]
  change projectiveTrace R ι n e
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n
      ((moduleExtCohomologyAddEquiv (ProjectiveSpace R ι) M n)
        ((moduleExtCohomologyAddEquiv (ProjectiveSpace R ι) M n).symm x))) = _
  rw [AddEquiv.apply_symm_apply]

/-- The canonical top Serre map on actual structure-linear morphisms. -/
def projectiveTopSerreMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
    (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))) →ₗ[R]
      Module.Dual R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
  exact (projectiveSerrePairing R ι n e M n 0 (Nat.add_zero n)).comp
    (Ext.linearEquiv₀ (R := R) (C := (ProjectiveSpace R ι).Modules)).symm.toLinearMap

/-- The top map is literally the original trace composed with the original cohomology map. -/
theorem projectiveTopSerreMap_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (f : M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
    projectiveTopSerreMap R ι n e M f x =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x) :=
  projectiveSerrePairing_mk₀ R ι n e M f x

/-- Coefficient naturality is the original module Ext precomposition and the original
actual-cohomology coefficient map, linked by native Yoneda associativity. -/
theorem projectiveSerrePairing_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} (f : M ⟶ N) (i j : ℕ) (hij : i + j = n)
    (y : Ext.{u + 1} N (twistingSheaf R ι (-(Fintype.card ι : ℤ))) j)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) i) :
    projectiveSerrePairing R ι n e M i j hij ((Ext.mk₀ f).comp y (Nat.zero_add j)) x =
      projectiveSerrePairing R ι n e N i j hij y
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) i x) := by
  let EM := moduleExtCohomologyAddEquiv (ProjectiveSpace R ι) M i
  let EN := moduleExtCohomologyAddEquiv (ProjectiveSpace R ι) N i
  have hcoeff : EN.symm
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) i x) =
        (EM.symm x).comp (Ext.mk₀ f) (Nat.add_zero i) := by
    apply EN.injective
    rw [AddEquiv.apply_symm_apply]
    have h := moduleExtCohomologyMap_naturality (ProjectiveSpace R ι) f i (EM.symm x)
    change EN ((EM.symm x).comp (Ext.mk₀ f) (Nat.add_zero i)) =
      Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) i
        (EM (EM.symm x)) at h
    rw [AddEquiv.apply_symm_apply] at h
    exact h.symm
  rw [projectiveSerrePairing_apply, projectiveSerrePairing_apply]
  change projectiveTrace R ι n e (moduleExtCohomologyMap (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
        ((EM.symm x).comp ((Ext.mk₀ f).comp y (Nat.zero_add j)) hij)) =
    projectiveTrace R ι n e (moduleExtCohomologyMap (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
        ((EN.symm (Sheaf.H.map
          ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) i x)).comp y hij))
  rw [hcoeff]
  exact congrArg (fun z => projectiveTrace R ι n e (moduleExtCohomologyMap
    (ProjectiveSpace R ι) (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n z))
    (Ext.comp_assoc_of_second_deg_zero (EM.symm x) (Ext.mk₀ f) y hij).symm

/-- The canonical top map commutes with the original coefficient maps. -/
theorem projectiveTopSerreMap_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} (f : M ⟶ N)
    (g : N ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
    projectiveTopSerreMap R ι n e M (f ≫ g) x =
      projectiveTopSerreMap R ι n e N g
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x) := by
  rw [projectiveTopSerreMap_apply, projectiveTopSerreMap_apply]
  congr 1
  rw [Functor.map_comp, Sheaf.H.map_comp_apply]

end AlgebraicGeometry.Scheme.Cohomology
