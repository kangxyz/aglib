/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineHomRecovery
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemFactorization

/-! # Affine formal comparison through an arbitrary inverse diagram

The formal-functions input is bijectivity of the original comparison on
compatible sections. The output is a morphism in the original coherent adic
category with its entire comparison diagram and whole-family uniqueness.
Only the source and genuine target are compatible adic systems.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u v
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} (F G : AdicSystem (Spec B) K)
  {T : ℕᵒᵖ ⥤ ModuleCat.{v} B}
  (ψ : ∀ j, G.affineSectionsTower.obj j →ₗ[B] T.obj j)
  (hψ : ∀ {j k} (a : j ⟶ k) x,
    ψ k (G.affineSectionsTower.map a x) = T.map a (ψ j x))
  (hψb : Function.Bijective (ModuleCat.sectionsMapOfLinearMaps ψ hψ))
  (γ : ∀ j, F.affineSectionsTower.obj j →ₗ[B] T.obj j)
  (hγ : ∀ {j k} (a : j ⟶ k) x,
    γ k (F.affineSectionsTower.map a x) = T.map a (γ j x))

/-- Original affine formal comparison supplied by the original limit isomorphism. -/
def affineFormalComparison : F ⟶ G :=
  F.affineHomOfFamily G
    (fun j => F.affineSections_isCompatibleSystem.factorizationStage
      G.affineSections_isCompatibleSystem (IsNoetherian.noetherian _) ψ hψ hψb γ hγ j.unop)
    (fun a x => F.affineSections_isCompatibleSystem.factorizationStage_naturality
      G.affineSections_isCompatibleSystem (IsNoetherian.noetherian _) ψ hψ hψb γ hγ a x)

/-- Every original affine stage has the required comparison diagram. -/
theorem affineFormalComparison_diagram (j : ℕᵒᵖ) (x : F.affineSectionsTower.obj j) :
    ψ j (moduleSpecΓFunctor.map
      ((F.affineFormalComparison G ψ hψ hψb γ hγ).hom.app j) x) = γ j x := by
  rw [affineFormalComparison, affineHomOfFamily_map (hq := fun a x =>
    F.affineSections_isCompatibleSystem.factorizationStage_naturality
      G.affineSections_isCompatibleSystem (IsNoetherian.noetherian _) ψ hψ hψb γ hγ a x)]
  exact F.affineSections_isCompatibleSystem.factorizationStage_comparison
    G.affineSections_isCompatibleSystem (IsNoetherian.noetherian _) ψ hψ hψb γ hγ j.unop x

/-- The equations determine the WHOLE original formal map, not a single stage
independently of transition compatibility. -/
theorem affineFormalComparison_unique (α : F ⟶ G)
    (hα : ∀ j x, ψ j (moduleSpecΓFunctor.map (α.hom.app j) x) = γ j x) :
    α = F.affineFormalComparison G ψ hψ hψb γ hγ := by
  apply F.affineHom_ext G
  intro j
  rw [affineFormalComparison, affineHomOfFamily_map (hq := fun a x =>
    F.affineSections_isCompatibleSystem.factorizationStage_naturality
      G.affineSections_isCompatibleSystem (IsNoetherian.noetherian _) ψ hψ hψb γ hγ a x)]
  apply ModuleCat.hom_ext
  exact F.affineSections_isCompatibleSystem.factorizationStage_unique
    G.affineSections_isCompatibleSystem (IsNoetherian.noetherian _) ψ hψ hψb γ hγ
    (fun k => (moduleSpecΓFunctor.map (α.hom.app k)).hom)
    (fun a x => ConcreteCategory.congr_hom
      ((Functor.whiskerRight α.hom moduleSpecΓFunctor).naturality a) x)
    hα j.unop

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
