/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Restriction

/-!
# Exterior coefficients along an arbitrary scheme morphism

This is the sole generic implementation extracted from the original
`Cohomology.Duality.Projective.DifferentialTrace.Restriction` helper block.
The proof bodies, sectionwise wedges and original scalar maps are unchanged.
It does not require an open immersion, flatness, or local freeness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical exterior wedge on the original open sections. -/
def wedgeAt (X : Scheme.{u}) (N : X.Modules) (n : ℕ) (U : X.Opens) :
    Γ(N, U) [⋀^Fin n]→ₗ[Γ(X, U)] Γ(moduleExteriorPower X N n, U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf N n).app (op U)

/-- The canonical wedge commutes with the original section restrictions. -/
theorem wedgeAt_naturality (X : Scheme.{u}) (N : X.Modules) (n : ℕ)
    {U V : X.Opens} (p : U ⟶ V) (s : Fin n → Γ(N, V)) :
    (moduleExteriorPower X N n).presheaf.map p.op (wedgeAt X N n V s) =
      wedgeAt X N n U (fun i => N.presheaf.map p.op (s i)) :=
  SheafOfModulesOfCommRing.exteriorPowerMk_naturality X.sheaf N n p.op s

/-- The original coefficient morphism evaluated on an actual open. -/
def coefficientSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (x : Γ(M, U)) : Γ(N, g ⁻¹ᵁ U) := (φ.app U).hom x

/-- The original coefficient section map is additive. -/
theorem coefficientSection_add {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (x y : Γ(M, U)) :
    coefficientSection (M := M) (N := N) g φ U (x + y) =
      coefficientSection (M := M) (N := N) g φ U x +
        coefficientSection (M := M) (N := N) g φ U y :=
  map_add (φ.app U).hom x y

/-- The original coefficient section map uses the original structure scalar map. -/
theorem coefficientSection_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (r : Γ(Y, U)) (x : Γ(M, U)) :
    coefficientSection (M := M) (N := N) g φ U (r • x) =
      g.app U r • coefficientSection (M := M) (N := N) g φ U x :=
  (φ.val.app' (op U)).hom.map_smul r x

/-- The compatible exterior coefficient family for any original scheme morphism. -/
def exteriorCoefficientAlternating {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (n : ℕ) :
    PresheafOfModulesOfCommRing.AlternatingMap M.val
      ((Scheme.Modules.pushforward g).obj (moduleExteriorPower X N n)).val n where
  app U := {
    toFun := fun v => wedgeAt X N n (g ⁻¹ᵁ U.unop)
      (coefficientSection (M := M) (N := N) g φ U.unop ∘ v)
    map_update_add' := fun v i x y => by
      change wedgeAt X N n (g ⁻¹ᵁ U.unop)
        (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i (x + y)) =
        wedgeAt X N n (g ⁻¹ᵁ U.unop)
          (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i x) +
          wedgeAt X N n (g ⁻¹ᵁ U.unop)
            (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i y)
      simp only [Function.comp_update]
      rw [coefficientSection_add (M := M) (N := N) g φ]
      exact (wedgeAt X N n (g ⁻¹ᵁ U.unop)).map_update_add _ i _ _
    map_update_smul' := fun v i r x => by
      change wedgeAt X N n (g ⁻¹ᵁ U.unop)
        (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i (r • x)) =
        g.app U.unop r • wedgeAt X N n (g ⁻¹ᵁ U.unop)
          (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i x)
      simp only [Function.comp_update]
      rw [coefficientSection_smul (M := M) (N := N) g φ]
      exact (wedgeAt X N n (g ⁻¹ᵁ U.unop)).map_update_smul _ i _ _
    map_eq_zero_of_eq' := fun v i j h hij =>
      (wedgeAt X N n (g ⁻¹ᵁ U.unop)).map_eq_zero_of_eq _
          (congrArg (coefficientSection (M := M) (N := N) g φ U.unop) h) hij }
  naturality {U V} p s := by
    change (moduleExteriorPower X N n).presheaf.map
        ((Opens.map g.base).map p.unop).op
        (wedgeAt X N n (g ⁻¹ᵁ U.unop)
          (coefficientSection (M := M) (N := N) g φ U.unop ∘ s)) =
      wedgeAt X N n (g ⁻¹ᵁ V.unop)
        (fun i => coefficientSection (M := M) (N := N) g φ V.unop (M.presheaf.map p (s i)))
    rw [wedgeAt_naturality]
    congr 1
    funext i
    exact (PresheafOfModules.naturality_apply φ.val p (s i)).symm

/-- The exterior coefficient morphism induced by the original compatible wedge family. -/
def exteriorCoefficientMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (n : ℕ) :
    moduleExteriorPower Y M n ⟶ (Scheme.Modules.pushforward g).obj (moduleExteriorPower X N n) :=
  SheafOfModulesOfCommRing.exteriorPowerDesc Y.sheaf M _ n
    (exteriorCoefficientAlternating (M := M) (N := N) g φ n)

end AlgebraicGeometry.Scheme.Modules
