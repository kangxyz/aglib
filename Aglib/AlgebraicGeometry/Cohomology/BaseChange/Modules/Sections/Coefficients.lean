/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Basic

/-! # Coefficient naturality of the original section tensor map

Native scalar restriction of the original module-presheaf forgetful functor
supplies the coefficient functor. Its objects are literally the existing
`moduleSectionsPresheaf`; no replacement section objects are constructed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
  (p : Y ⟶ X) (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤)) (σ : A →+* B)
  (hσ : p.appTop.hom.comp α = β.comp σ)

/-- The original scalar section mate is natural in an actual target coefficient map. -/
theorem moduleSectionsTensorMapAlong_comp_app {M : X.Modules} {N N' : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ψ : N ⟶ N') (U : X.Opensᵒᵖ) :
    (moduleSectionsTensorMapAlong p α β σ hσ
      (φ ≫ (Scheme.Modules.pushforward p).map ψ)).app U =
      (moduleSectionsTensorMapAlong p α β σ hσ φ).app U ≫
        ((moduleSectionsPresheafFunctor Y β).map ψ).app (op (p ⁻¹ᵁ U.unop)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  erw [moduleSectionsTensorMapAlong_one_tmul p α β σ hσ
    (φ ≫ (Scheme.Modules.pushforward p).map ψ) U.unop m]
  change ψ.app (p ⁻¹ᵁ U.unop) (φ.app U.unop m) =
    ψ.app (p ⁻¹ᵁ U.unop)
      ((moduleSectionsTensorMapAlong p α β σ hσ φ).app U ((1 : B) ⊗ₜ[A,σ] m))
  erw [moduleSectionsTensorMapAlong_one_tmul p α β σ hσ φ U.unop m]

end AlgebraicGeometry.Scheme.Cohomology
