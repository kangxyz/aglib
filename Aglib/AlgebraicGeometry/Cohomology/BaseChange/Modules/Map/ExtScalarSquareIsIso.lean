/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.ExtScalarSquare.VerticalIsIso

/-! # Invertibility through the original open scalar restriction square

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

/-- Invertibility of the original restricted tensor mate transports through the
original open square, with its vertical isomorphisms supplied by restriction. -/
theorem moduleHPrimeTensorMap_isIso_app_of_restricted_tensor_isIso
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ) (M : X.Modules) (U : X.Opens) (n : ℕ)
    (hδ : let V := p ⁻¹ᵁ U
      let a := V.ι
      let b := p ∣_ U
      let j := U.ι
      let h := (isPullback_morphismRestrict p U).flip
      IsIso (moduleCohomologyTensorMap b σ (j.appTop.hom.comp α)
        (a.appTop.hom.comp β) (moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w)
        ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)) n)) :
    IsIso ((moduleHPrimeTensorMap p σ α β hσ
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n).app (op U)) := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let hopen : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let hs := hσ
  let αU := j.appTop.hom.comp α
  let βV := a.appTop.hom.comp β
  let hsU := moduleSectionsOpenSquare_scalars a b p j α β σ hs hopen.w
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  let δ := moduleCohomologyTensorMap b σ αU βV hsU φb n
  let : IsIso δ := hδ
  let square := moduleOpenPullbackExtTensorSquare p σ α β hs M U n
  let : IsIso square.f₁₃ :=
    moduleOpenPullbackExtTensorSquare_left_isIso p σ α β hs M U n
  let : IsIso square.f₂₄ :=
    moduleOpenPullbackExtTensorSquare_right_isIso p σ α β hs M U n
  have hbottom : square.f₃₄ = δ := by
    change (moduleOpenPullbackExtTensorSquare p σ α β hs M U n).f₃₄ = _
    dsimp only [moduleOpenPullbackExtTensorSquare]
    exact moduleHPrimeScalarOpenMap_comp_congr_top_square_bottom _ _ _ _ _ _ _ _ _ _
      σ α β hs U V.ι_preimage_self U.ι_preimage_self n
  let : IsIso square.f₃₄ := by rw [hbottom]; infer_instance
  have htop := square.isIso_top_of_other_edges
  change IsIso (moduleOpenPullbackExtTensorSquare p σ α β hs M U n).f₁₂ at htop
  rw [moduleOpenPullbackExtTensorSquare_top] at htop
  exact htop

end AlgebraicGeometry.Scheme.Cohomology
