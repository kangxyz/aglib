/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Nonzero

/-! # Original values of the scalar-restricted cohomology map

Restricting structural scalars packages the original geometric map; it does
not change its values. The degree-zero unit law retains that original package.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Cohomology

variable {R S : Type u} [CommRing R] [CommRing S]
  {X Y : Scheme.{u}} (p : X ⟶ Y) (σ : R →+* S)
  (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤))
  (h : p.appTop.hom.comp α = β.comp σ)

/-- The original scalar-restriction wrapper preserves every geometric class value. -/
theorem moduleCohomologyRestrictionMap_apply {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Modules.pushforward p).obj N) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    let := moduleCohomologyModuleOfHom Y α M n
    let := moduleCohomologyModuleOfHom X β N n
    moduleCohomologyRestrictionMap p σ α β h φ n x =
      moduleCohomologyMapAlong p φ n x := rfl

/-- At the original adjunction unit, the packaged value is literal pullback. -/
theorem moduleCohomologyRestrictionMap_unit_apply (M : Y.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    let := moduleCohomologyModuleOfHom Y α M n
    let := moduleCohomologyModuleOfHom X β ((Modules.pullback p).obj M) n
    moduleCohomologyRestrictionMap p σ α β h
      ((Modules.pullbackPushforwardAdjunction p).unit.app M) n x =
        moduleCohomologyPullback p M n x :=
  moduleCohomologyRestrictionMap_apply p σ α β h _ n x

/-- The original scalar-restricted unit map has the original H0 section value. -/
theorem moduleCohomologyRestrictionMap_unit_equivZero (M : Y.Modules)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0) :
    let := moduleCohomologyModuleOfHom Y α M 0
    let := moduleCohomologyModuleOfHom X β ((Modules.pullback p).obj M) 0
    Sheaf.H.equiv₀ (moduleAddSheaf X ((Modules.pullback p).obj M)) isTerminalTop
      (moduleCohomologyRestrictionMap p σ α β h
        ((Modules.pullbackPushforwardAdjunction p).unit.app M) 0 x) =
      ((Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
        (Sheaf.H.equiv₀ (moduleAddSheaf Y M) isTerminalTop x) := by
  let := moduleCohomologyModuleOfHom Y α M 0
  let := moduleCohomologyModuleOfHom X β ((Modules.pullback p).obj M) 0
  exact (congrArg
    (Sheaf.H.equiv₀ (moduleAddSheaf X ((Modules.pullback p).obj M)) isTerminalTop)
    (moduleCohomologyRestrictionMap_unit_apply p σ α β h M 0 x)).trans
      (moduleCohomologyPullback_equiv₀ (M := M) p x)

end AlgebraicGeometry.Scheme.Cohomology
