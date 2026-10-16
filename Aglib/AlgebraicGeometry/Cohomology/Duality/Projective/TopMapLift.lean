/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Pairing
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Canonical universe lifts of the original top Serre map

The native exact-diagram lemma uses one coefficient category. Original scheme morphisms
and actual cohomology duals can occupy different universes, so the former are lifted by
native `ULift` and the scalar target by the native module equivalence. The resulting map
is exactly the original top Serre map after `down`, and its bijectivity is equivalent to
that of the original map. No cohomology object or pairing is replaced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The native scalar-target lift identifies original cohomology duals with the actual
represented module morphisms into `ULift R`, without changing the original source. -/
def projectiveCohomologyDualLiftEquiv (M : (ProjectiveSpace R ι).Modules) (n : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
    Module.Dual R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) ≃ₗ[R]
      ((moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α n).obj M ⟶
        ModuleCat.of R (ULift.{u + 1} R)) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
  let H := (moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α n).obj M
  change Module.Dual R H ≃ₗ[R] (H ⟶ ModuleCat.of R (ULift.{u + 1} R))
  exact (LinearEquiv.arrowCongr (LinearEquiv.refl R H)
    ((ULift.moduleEquiv : ULift.{u + 1} R ≃ₗ[R] R).symm)).trans
      (ModuleCat.homLinearEquiv (R := R) (S := R)
        (M := H) (N := ModuleCat.of R (ULift.{u + 1} R))).symm

variable [Fintype ι]

/-- The original top map transported only by the native source and scalar-target universe
lifts, ready for a native exact diagram in one additive-group category. -/
def projectiveTopSerreLift (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    ULift.{u + 1} (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))) →ₗ[R]
      ((moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α n).obj M ⟶
        ModuleCat.of R (ULift.{u + 1} R)) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
  exact (projectiveCohomologyDualLiftEquiv R ι M n).toLinearMap.comp
    ((projectiveTopSerreMap R ι n e M).comp
      (ULift.moduleEquiv :
        ULift.{u + 1} (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))) ≃ₗ[R]
          (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))).toLinearMap)

/-- The lifted map is literally the native `up` of the original canonical top pairing. -/
theorem projectiveTopSerreLift_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (f : ULift.{u + 1} (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
    (projectiveTopSerreLift R ι n e M f).hom x =
      ULift.up (projectiveTopSerreMap R ι n e M f.down x) := rfl

/-- Native lifting retains original coefficient naturality exactly. -/
theorem projectiveTopSerreLift_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} (f : M ⟶ N)
    (g : ULift.{u + 1} (N ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))) :
    projectiveTopSerreLift R ι n e M (ULift.up (f ≫ g.down)) =
      (moduleCohomologyFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) n).map f ≫
          projectiveTopSerreLift R ι n e N g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.down_injective
  change projectiveTopSerreMap R ι n e M (f ≫ g.down) x =
    projectiveTopSerreMap R ι n e N g.down
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x)
  exact projectiveTopSerreMap_naturality R ι n e f g.down x

/-- Native universe lifts preserve and reflect bijectivity of the original top map. -/
theorem projectiveTopSerreLift_bijective_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) :
    Function.Bijective (projectiveTopSerreLift R ι n e M) ↔
      Function.Bijective (projectiveTopSerreMap R ι n e M) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
  let E := (ULift.moduleEquiv :
    ULift.{u + 1} (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))) ≃ₗ[R]
      (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))))
  let D := projectiveCohomologyDualLiftEquiv R ι M n
  change Function.Bijective (D ∘ projectiveTopSerreMap R ι n e M ∘ E) ↔ _
  exact (Function.Bijective.of_comp_iff' D.bijective _).trans
    (Function.Bijective.of_comp_iff _ E.bijective)

/-- Isomorphism of the native lifted additive-group map is exactly bijectivity of the
original structural-linear top Serre map. -/
theorem projectiveTopSerreLift_isIso_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    IsIso (AddCommGrpCat.ofHom (projectiveTopSerreLift R ι n e M).toAddMonoidHom) ↔
      Function.Bijective (projectiveTopSerreMap R ι n e M) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  rw [ConcreteCategory.isIso_iff_bijective]
  exact projectiveTopSerreLift_bijective_iff R ι n e M

end AlgebraicGeometry.Scheme.Cohomology
