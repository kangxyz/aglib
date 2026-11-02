/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.ExtScalarSquare.RestrictionMap
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.LinearCoefficients.IsIso
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Cartesian.Geometric
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionSquare

/-! # Complete vertical invertibility of the original open scalar square

The original restriction and cartesian coefficient isomorphisms supply both
vertical isomorphisms before structural ring maps are specialized. The original
restricted tensor mate then determines invertibility of the original open mate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original left edge is invertible by the original open restriction comparison. -/
theorem moduleOpenPullbackExtTensorSquare_left_isIso
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    IsIso (moduleOpenPullbackExtTensorSquare p σ α β hσ M U n).f₁₃ := by
  let αU := U.ι.appTop.hom.comp α
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict U.ι) n
  let eX : (moduleHPrimePresheaf X α M n).obj (op U) ≅
      ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict U.ι)) n) :=
    (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso
  have hleft : (moduleOpenPullbackExtTensorSquare p σ α β hσ M U n).f₁₃ =
      (ModuleCat.extendScalars σ).map eX.hom := by
    rw [moduleOpenPullbackExtTensorSquare_left]
    apply congrArg (ModuleCat.extendScalars σ).map
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U at x
    exact (moduleHPrimeOpenRestrictionAddEquiv_geometric X U M n x).symm
  rw [hleft]
  infer_instance

/-- The original right edge is invertible using its actual cartesian coefficient mate. -/
theorem moduleOpenPullbackExtTensorSquare_right_isIso
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    IsIso (moduleOpenPullbackExtTensorSquare p σ α β hσ M U n).f₂₄ := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let ε : N.restrict a ⟶ P :=
    inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
  rw [moduleOpenPullbackExtTensorSquare_right_map]
  exact moduleHPrimeRestrictionPostcompMap_isIso Y β V N ε n

end AlgebraicGeometry.Scheme.Cohomology
