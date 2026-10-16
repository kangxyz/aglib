/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The canonical scalar-extension map on actual module cohomology

A compatible change of structural rings and an actual geometric coefficient
arrow give a canonical tensor map on the original `Sheaf.H`. It is the mate
under the native extension/restriction adjunction of the geometric cohomology
map. Its unit and pure-tensor formulas identify the actual forward map.

Flatness and quasicoherence are not premises for constructing this map; they
belong to the subsequent invertibility theorem.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  {X Y : Scheme.{u}} (p : X ⟶ Y) (σ : R →+* S)
  (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤))
  (h : p.appTop.hom.comp α = β.comp σ)
  {M : Y.Modules} {N : X.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (n : ℕ)

/-- The actual geometric cohomology map, viewed after restriction of structural scalars. -/
def moduleCohomologyRestrictionMap :
    letI := moduleCohomologyModuleOfHom Y α M n
    letI := moduleCohomologyModuleOfHom X β N n
    ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) ⟶
      (ModuleCat.restrictScalars σ).obj
        (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf X N) n)) := by
  letI := moduleCohomologyModuleOfHom Y α M n
  letI := moduleCohomologyModuleOfHom X β N n
  refine ModuleCat.ofHom
    (X := ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) n))
    (Y := (ModuleCat.restrictScalars σ).obj
      (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf X N) n))) {
    __ := moduleCohomologyMapAlong p φ n
    map_smul' := fun a x ↦ ?_ }
  change moduleCohomologyMapAlong p φ n
      (Sheaf.H.map (moduleScalarOfGlobal Y M (α a)) n x) =
    Sheaf.H.map (moduleScalarOfGlobal X N (β (σ a))) n
      (moduleCohomologyMapAlong p φ n x)
  have ha : p.appTop (α a) = β (σ a) := congrArg (fun q : R →+* Γ(X, ⊤) ↦ q a) h
  rw [← ha]
  exact zariskiCohomologyMap_naturality p _ _ (moduleCoefficientPullback p φ)
    (moduleScalarOfGlobal Y M (α a))
    (moduleScalarOfGlobal X N (p.appTop (α a)))
    (moduleCoefficientPullback_scalar p φ (α a)) n x

/-- The original scalar-extension mate of geometric cohomology with arbitrary coefficients. -/
def moduleCohomologyTensorMap :
    letI := moduleCohomologyModuleOfHom Y α M n
    letI := moduleCohomologyModuleOfHom X β N n
    (ModuleCat.extendScalars σ).obj
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) n)) ⟶
      ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf X N) n) := by
  letI := moduleCohomologyModuleOfHom Y α M n
  letI := moduleCohomologyModuleOfHom X β N n
  exact ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).symm
    (moduleCohomologyRestrictionMap p σ α β h φ n)

/-- The tensor map retains the original extension/restriction adjunction unit. -/
theorem moduleCohomologyTensorMap_unit :
    let := moduleCohomologyModuleOfHom Y α M n
    let := moduleCohomologyModuleOfHom X β N n
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).unit.app
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) n)) ≫
      (ModuleCat.restrictScalars σ).map (moduleCohomologyTensorMap p σ α β h φ n) =
        moduleCohomologyRestrictionMap p σ α β h φ n := by
  let := moduleCohomologyModuleOfHom Y α M n
  let := moduleCohomologyModuleOfHom X β N n
  exact Equiv.apply_symm_apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _) _

/-- On the unit pure tensor, the canonical map is exactly geometric cohomology pullback. -/
theorem moduleCohomologyTensorMap_one_tmul
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    let := moduleCohomologyModuleOfHom Y α M n
    let := moduleCohomologyModuleOfHom X β N n
    moduleCohomologyTensorMap p σ α β h φ n ((1 : S) ⊗ₜ[R,σ] x) =
      moduleCohomologyMapAlong p φ n x := by
  let := moduleCohomologyModuleOfHom Y α M n
  let := moduleCohomologyModuleOfHom X β N n
  exact congrArg (fun q ↦ q x) (moduleCohomologyTensorMap_unit p σ α β h φ n)

end AlgebraicGeometry.Scheme.Cohomology
