/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.FunctionField.UnitOpen
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Charts

/-!
# Smooth affine constants and the canonical generic constants map

Source retains actual affine structural constants and generic-germ equations under smoothness.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Smooth.Constants`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`aad28c7eb7f40f601eddbb5335bc184e1aa5c80bcda32eeebdf49e7ce30ccb8b`. Selected lines: [[16, 65]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
namespace AlgebraicGeometry.Scheme
universe u
open _root_.AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

/-- Constants on the actual affine open, from its original structure map. -/
def chartConstantMap (K : Type u) [Field K] (X : Scheme.{u})
    (p : X ⟶ Spec (.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appLE ⊤ U (by simp)).hom

/-- Smoothness of the chart algebra is derived from the actual smooth scheme
morphism, rather than supplied as a new model assumption. -/
theorem chartConstantMap_smooth (K : Type u) [Field K] (X : Scheme.{u})
    (p : X ⟶ Spec (.of K)) [_root_.AlgebraicGeometry.Smooth p]
    (U : X.Opens) (hU : IsAffineOpen U) : (chartConstantMap K X p U).Smooth := by
  dsimp only [chartConstantMap]
  rw [CommRingCat.hom_comp, RingHom.Smooth.respectsIso.cancel_left_isIso]
  exact p.smooth_appLE (isAffineOpen_top _) hU (by simp)


open _root_.AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

local instance nonemptyTop (X : Scheme.{u}) [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The original structure morphism supplies the generic constant-field map. -/
abbrev genericConstantMap (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (.of K)) : K →+* X.functionField :=
  X.functionFieldConstants p

/-- Restriction of the actual constant section map. -/
theorem chartConstantMap_restrict (K : Type u) [Field K] (X : Scheme.{u})
    (p : X ⟶ Spec (.of K)) (U : X.Opens) :
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
      (chartConstantMap K X p ⊤) = chartConstantMap K X p U := by
  have hmap := p.appLE_map (show (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤ by simp)
    (homOfLE (show U ≤ ⊤ from le_top)).op
  have hcomp := congrArg
    (fun f => (Scheme.ΓSpecIso (.of K)).inv ≫ f) hmap
  exact congrArg CommRingCat.Hom.hom ((Category.assoc _ _ _).trans hcomp)

/-- Every selected nonempty chart uses the same original generic constant
map; this identifies the constant root before and after chart selection. -/
theorem chart_genericConstantMap (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (.of K)) (U : X.Opens) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (chartConstantMap K X p U) =
      genericConstantMap K X p := by
  ext x
  have hres := RingHom.congr_fun (chartConstantMap_restrict K X p U) x
  have hg : X.germToFunctionField U (chartConstantMap K X p U x) =
      X.germToFunctionField ⊤ (chartConstantMap K X p ⊤ x) := by
    rw [← hres]
    exact X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top))
      (genericPoint X) (genericPoint_mem_nonempty_open X U) (chartConstantMap K X p ⊤ x)
  have htop : chartConstantMap K X p ⊤ =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom := by
    have happ : p.appLE ⊤ ⊤ (by simp) = p.appTop := p.appLE_eq_app
    exact congrArg (fun f => ((Scheme.ΓSpecIso (.of K)).inv ≫ f).hom) happ
  rw [htop] at hg
  exact hg

end AlgebraicGeometry.Scheme
