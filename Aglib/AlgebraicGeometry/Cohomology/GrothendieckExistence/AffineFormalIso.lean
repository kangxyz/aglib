/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineFormalComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineEffectivityHom

/-! # Detection of original affine formal isomorphisms on compatible sections -/

@[expose] public noncomputable section
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F G : AdicSystem (Spec B) K}

/-- Bijectivity on original compatible sections detects an isomorphism of
actual coherent adic systems. Only the two genuine adic systems are used. -/
theorem isIso_of_affineFormalSectionsMap_bijective (φ : F ⟶ G)
    (hφ : Function.Bijective (affineFormalSectionsMap φ)) : IsIso φ := by
  let ψ := fun j => (affineSectionsMap φ).app j |>.hom
  have hψ : ∀ {j k} (a : j ⟶ k) x,
      ψ k (F.affineSectionsTower.map a x) = G.affineSectionsTower.map a (ψ j x) :=
    fun a x => ConcreteCategory.congr_hom ((affineSectionsMap φ).naturality a) x
  have hb : Function.Bijective (ModuleCat.sectionsMapOfLinearMaps ψ hψ) := hφ
  let γ := fun j => LinearMap.id (R := B) (M := G.affineSectionsTower.obj j)
  have hγ : ∀ {j k} (a : j ⟶ k) x,
      γ k (G.affineSectionsTower.map a x) = G.affineSectionsTower.map a (γ j x) :=
    fun _ _ => rfl
  let β := G.affineFormalComparison F ψ hψ hb γ hγ
  have hr : β ≫ φ = 𝟙 G := by
    apply G.affineHom_ext G
    intro j
    apply ModuleCat.hom_ext
    ext x
    exact G.affineFormalComparison_diagram F ψ hψ hb γ hγ j x
  have hl : φ ≫ β = 𝟙 F := by
    have hleft := F.affineFormalComparison_unique F ψ hψ hb ψ hψ (φ ≫ β)
      (by
        intro j x
        have he := congrArg (fun a => moduleSpecΓFunctor.map (a.hom.app j) x)
          (show (φ ≫ β) ≫ φ = φ by rw [Category.assoc, hr, Category.comp_id])
        exact he)
    have hid := F.affineFormalComparison_unique F ψ hψ hb ψ hψ (𝟙 F)
      (by intro j x; rfl)
    exact hleft.trans hid.symm
  exact ⟨⟨β, hl, hr⟩⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
