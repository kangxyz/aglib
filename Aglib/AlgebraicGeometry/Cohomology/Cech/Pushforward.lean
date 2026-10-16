/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules

/-!
# Actual cohomology comparison for a direct image on affine covers

For the identity coefficient arrow `f_* M ⟶ f_* M`, the original geometric Cech map is
the native pushforward Cech isomorphism. If the displayed target cover and its preimage
have affine tuple intersections and the coefficients are quasicoherent, the original
geometric cohomology map is bijective in every degree. Degree zero uses the original
global-section comparison. Specified structural scalars give the corresponding linear
equivalence, with no extra cohomological comparison hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)

/-- The original identity direct-image coefficient gives exactly the native geometric
Cech pushforward isomorphism. No affineness or quasicoherence is needed for this identity. -/
theorem additiveCechGeometricMap_pushforward {ι : Type u} (U : ι → Y.Opens) :
    additiveCechGeometricMap f U
        (moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj M)) (moduleAddSheaf X M)
        (moduleCoefficientPullback f (𝟙 ((Scheme.Modules.pushforward f).obj M))) =
      (additiveCechPushforwardIso f U).hom.app (moduleAddSheaf X M) := by
  unfold additiveCechGeometricMap moduleCoefficientPullback
  rw [Equiv.apply_symm_apply]
  simp only [modulePushforwardAddSheafIso, Iso.refl_hom]
  have hid : (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) =
      𝟙 (moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj M)) :=
    (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map_id _
  rw [hid, Category.id_comp, (additiveCechFunctor Y U).map_id, Category.id_comp]

/-- In degree zero the original direct-image cohomology map is bijective for every
scheme morphism and every module, by its unchanged global-section formula. -/
theorem moduleCohomologyPushforwardMap_bijective_zero :
    Function.Bijective
      (moduleCohomologyMapAlong f (𝟙 ((Scheme.Modules.pushforward f).obj M)) 0) := by
  let eY := Sheaf.H.equiv₀
    (moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj M)) isTerminalTop
  let eX := Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop
  let eΓ := ((pushforwardSectionsIso f).app (moduleAddSheaf X M)).addCommGroupIsoToAddEquiv
  let E := eY.trans (eΓ.trans eX.symm)
  have hE : ∀ x, moduleCohomologyMapAlong f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) 0 x = E x := by
    intro x
    apply eX.injective
    have h := moduleCohomologyMapAlong_equiv₀ f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) x
    change eX (moduleCohomologyMapAlong f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) 0 x) = eΓ (eY x) at h
    change eX (moduleCohomologyMapAlong f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) 0 x) = eX (eX.symm (eΓ (eY x)))
    exact h.trans (eX.apply_symm_apply (eΓ (eY x))).symm
  have hfun : (moduleCohomologyMapAlong f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) 0 : _ → _) = E := funext hE
  rw [hfun]
  exact E.bijective

variable [M.IsQuasicoherent] [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
  {ι : Type u} (U : ι → Y.Opens) (hcover : iSup U = ⊤)
  (hcover' : (⨆ i, f ⁻¹ᵁ U i) = ⊤)
  (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
  (haff' : ∀ (p : ℕ) (a : Fin (p + 1) → ι),
    IsAffineOpen (∏ᶜ fun k => f ⁻¹ᵁ U (a k)))

include U hcover hcover' haff haff'

/-- The actual positive-degree direct-image cohomology map is bijective when the displayed
cover and its preimage have affine tuple intersections. -/
theorem moduleCohomologyPushforwardMap_bijective_succ (n : ℕ) :
    Function.Bijective
      (moduleCohomologyMapAlong f (𝟙 ((Scheme.Modules.pushforward f).obj M)) (n + 1)) := by
  let I := injectiveResolution (moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj M))
  let J := injectiveResolution (moduleAddSheaf X M)
  let eY := moduleCechCohomologyAddEquiv U ((Scheme.Modules.pushforward f).obj M)
    I hcover haff n
  let eX := moduleCechCohomologyAddEquiv (fun i => f ⁻¹ᵁ U i) M J hcover' haff' n
  let C := (additiveCechPushforwardIso f U).app (moduleAddSheaf X M)
  let CH := (homologyFunctor AddCommGrpCat.{u} (.up ℕ) (n + 1)).mapIso C
  let eH := CH.addCommGroupIsoToAddEquiv
  let E := eY.symm.trans (eH.trans eX)
  have hE : ∀ x, moduleCohomologyMapAlong f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) (n + 1) x = E x := by
    intro x
    have h := moduleCechCohomologyAddEquiv_geometric f U
      ((Scheme.Modules.pushforward f).obj M) M I J hcover hcover' haff haff'
      (moduleCoefficientPullback f (𝟙 ((Scheme.Modules.pushforward f).obj M))) n (eY.symm x)
    rw [additiveCechGeometricMap_pushforward, AddEquiv.apply_symm_apply] at h
    exact h.symm
  have hfun : (moduleCohomologyMapAlong f
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) (n + 1) : _ → _) = E := funext hE
  rw [hfun]
  exact E.bijective

/-- The original geometric direct-image cohomology map is bijective in every degree under
the explicit affine-cover hypotheses, with no supplied cohomology equivalence. -/
theorem moduleCohomologyPushforwardMap_bijective (n : ℕ) :
    Function.Bijective
      (moduleCohomologyMapAlong f (𝟙 ((Scheme.Modules.pushforward f).obj M)) n) := by
  cases n with
  | zero => exact moduleCohomologyPushforwardMap_bijective_zero f M
  | succ n =>
    exact moduleCohomologyPushforwardMap_bijective_succ f M U hcover hcover'
      haff haff' n

/-- The original direct-image cohomology map, as a linear equivalence for any specified
structural ring map and its actual pullback on global functions. -/
def moduleCohomologyPushforwardLinearEquiv {R : Type u} [CommRing R]
    (α : R →+* Γ(Y, ⊤)) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α ((Scheme.Modules.pushforward f).obj M) n
    letI := moduleCohomologyModuleOfHom X (f.appTop.hom.comp α) M n
    Sheaf.H.{u + 1} (moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj M)) n ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  letI := moduleCohomologyModuleOfHom Y α ((Scheme.Modules.pushforward f).obj M) n
  letI := moduleCohomologyModuleOfHom X (f.appTop.hom.comp α) M n
  exact LinearEquiv.ofBijective
    (moduleCohomologyMapAlongLinear f α (𝟙 ((Scheme.Modules.pushforward f).obj M)) n)
    (moduleCohomologyPushforwardMap_bijective f M U hcover hcover' haff haff' n)

/-- The proved linear equivalence has the original geometric cohomology map as its
literal forward function. -/
theorem moduleCohomologyPushforwardLinearEquiv_apply {R : Type u} [CommRing R]
    (α : R →+* Γ(Y, ⊤)) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj M)) n) :
    moduleCohomologyPushforwardLinearEquiv f M U hcover hcover' haff haff' α n x =
      moduleCohomologyMapAlong f (𝟙 ((Scheme.Modules.pushforward f).obj M)) n x := rfl

end AlgebraicGeometry.Scheme.Cohomology
