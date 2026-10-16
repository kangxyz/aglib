/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Actual cohomology of finite coproducts of projective twists

The original scalar-valued cohomology functor is additive. Its native finite-coproduct
comparison therefore expresses the cohomology of an actual finite sum of twists as the
finite sum of their original cohomology modules. In particular these modules are finite
and free over every commutative base ring, in every degree and for every integer twist.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) {I : Type u} [Finite I]

/-- Original cohomology of a finite native twist coproduct is the native finitely supported
sum of the original cohomology modules, with the structural base-ring actions. -/
def twistingCoproductCohomologyLinearEquiv (d : I → ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (∐ fun a => twistingSheaf R ι (d a)) q
    Sheaf.H.{u + 1}
        (moduleAddSheaf (ProjectiveSpace R ι) (∐ fun a => twistingSheaf R ι (d a))) q ≃ₗ[R]
      (Π₀ a : I, (moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q).obj
        (twistingSheaf R ι (d a))) := by
  classical
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (∐ fun a => twistingSheaf R ι (d a)) q
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q
  exact (PreservesCoproduct.iso H (fun a => twistingSheaf R ι (d a)) ≪≫
    ModuleCat.coprodIsoDirectSum.{u, u, u + 1}
      (fun a => H.obj (twistingSheaf R ι (d a)))).toLinearEquiv

open Classical in
/-- The finite-sum comparison retains the original cohomology map of each actual summand
inclusion; its value is the literal native single component. -/
theorem twistingCoproductCohomologyLinearEquiv_inclusion (d : I → ℤ) (q : ℕ) (a : I)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι (d a))) q) :
    twistingCoproductCohomologyLinearEquiv R ι d q
        (Sheaf.H.map ((SheafOfModules.toSheaf.{u} (ProjectiveSpace R ι).ringCatSheaf).map
          (Sigma.ι (fun b => twistingSheaf R ι (d b)) a)) q x) = DFinsupp.single a x := by
  classical
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q
  let F : I → (ProjectiveSpace R ι).Modules := fun b => twistingSheaf R ι (d b)
  have hi : H.map (Sigma.ι F a) ≫ (PreservesCoproduct.iso H F).hom =
      Sigma.ι (fun b => H.obj (F b)) a := by
    rw [← cancel_mono (PreservesCoproduct.iso H F).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  change (H.map (Sigma.ι F a) ≫ (PreservesCoproduct.iso H F).hom ≫
    (ModuleCat.coprodIsoDirectSum.{u, u, u + 1} (fun b => H.obj (F b))).hom) x = _
  rw [← Category.assoc, hi, ModuleCat.ι_coprodIsoDirectSum_hom]
  rfl

/-- Every cohomology module of a finite sum of twists is finite over the original base ring.
The explicit coordinate labeling retains arbitrary ring and scheme universes. -/
theorem twistingCoproductCohomology_finite (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : I → ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (∐ fun a => twistingSheaf R ι (d a)) q
    Module.Finite R (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι) (∐ fun a => twistingSheaf R ι (d a))) q) := by
  classical
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (∐ fun a => twistingSheaf R ι (d a)) q
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q
  let : ∀ a : I, Module.Finite R (H.obj (twistingSheaf R ι (d a))) :=
    fun a => twistingCohomology_finite R ι n e (d a) q
  exact Module.Finite.equiv (twistingCoproductCohomologyLinearEquiv R ι d q).symm

/-- The same original cohomology modules of finite twist coproducts are free over the base. -/
theorem twistingCoproductCohomology_free (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : I → ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (∐ fun a => twistingSheaf R ι (d a)) q
    Module.Free R (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι) (∐ fun a => twistingSheaf R ι (d a))) q) := by
  classical
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (∐ fun a => twistingSheaf R ι (d a)) q
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q
  let : ∀ a : I, Module.Free R (H.obj (twistingSheaf R ι (d a))) :=
    fun a => twistingCohomology_free R ι n e (d a) q
  exact Module.Free.of_equiv (twistingCoproductCohomologyLinearEquiv R ι d q).symm

/-- A finite sum of twists obeys the same sharp positive-degree vanishing bound when every
original summand degree does. The cohomology object is the unchanged native `Sheaf.H`. -/
theorem twistingCoproductCohomology_subsingleton_of_neg_le_degree
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : I → ℤ) (q : ℕ)
    (hd : ∀ a, -(n : ℤ) ≤ d a) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι) (∐ fun a => twistingSheaf R ι (d a))) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q
  let : ∀ a : I, Subsingleton (H.obj (twistingSheaf R ι (d a))) :=
    fun a => twistingCohomology_subsingleton_of_neg_le_degree R ι n e (d a) q (hd a) hq
  exact (twistingCoproductCohomologyLinearEquiv R ι d q).injective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
