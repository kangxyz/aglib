/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologySections
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Pushforward

/-!
# Canonical section comparison followed by affine direct image

The comparison is the original cohomology map of the given section
isomorphism followed by the original affine-pushforward cohomology map.
Explicit cover hypotheses are retained; no new comparison premise is hidden.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  (p : Y ⟶ X) (α : A →+* Γ(X, ⊤)) (F : X.Modules) (G : Y.Modules)
  [G.IsQuasicoherent] [((Scheme.Modules.pushforward p).obj G).IsQuasicoherent]
  {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (hcover' : (⨆ i, p ⁻¹ᵁ U i) = ⊤)
  (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
  (haff' : ∀ (q : ℕ) (a : Fin (q + 1) → ι),
    IsAffineOpen (∏ᶜ fun k => p ⁻¹ᵁ U (a k)))

/-- A natural comparison with direct-image sections computes original cohomology. -/
def moduleSectionsPushforwardCohomologyEquiv
    (e : moduleSectionsPresheaf X α F ≅
      moduleSectionsPresheaf X α ((Scheme.Modules.pushforward p).obj G)) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom X α F q
    letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
    Sheaf.H.{u + 1} (moduleAddSheaf X F) q ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf Y G) q := by
  letI := moduleCohomologyModuleOfHom X α F q
  letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
  letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
  exact (moduleSectionsCohomologyEquiv X α e q).trans
    (moduleCohomologyPushforwardLinearEquiv p G U hcover hcover' haff haff' α q)

/-- The composite retains both original maps on the nose. -/
theorem moduleSectionsPushforwardCohomologyEquiv_apply
    (e : moduleSectionsPresheaf X α F ≅
      moduleSectionsPresheaf X α ((Scheme.Modules.pushforward p).obj G)) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X F) q) :
    moduleSectionsPushforwardCohomologyEquiv p α F G U hcover hcover' haff haff' e q x =
      moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
        (Sheaf.H.map (moduleSectionsAddSheafMap X α e.hom) q x) := rfl

/-- Degree zero is precisely the given global section comparison and direct-image identity. -/
theorem moduleSectionsPushforwardCohomologyEquiv_equiv₀
    (e : moduleSectionsPresheaf X α F ≅
      moduleSectionsPresheaf X α ((Scheme.Modules.pushforward p).obj G))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X F) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf Y G) isTerminalTop
      (moduleSectionsPushforwardCohomologyEquiv p α F G U hcover hcover' haff haff' e 0 x) =
      (pushforwardSectionsIso p).hom.app (moduleAddSheaf Y G)
        (e.hom.app (op ⊤) (Sheaf.H.equiv₀ (moduleAddSheaf X F) isTerminalTop x)) := by
  rw [moduleSectionsPushforwardCohomologyEquiv_apply, moduleCohomologyMapAlong_equiv₀]
  have hid := (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_id
    ((Scheme.Modules.pushforward p).obj G)
  rw [hid]
  change (pushforwardSectionsIso p).hom.app (moduleAddSheaf Y G)
    (Sheaf.H.equiv₀ (moduleAddSheaf X ((Scheme.Modules.pushforward p).obj G))
      isTerminalTop (Sheaf.H.map (moduleSectionsAddSheafMap X α e.hom) 0 x)) = _
  have he := moduleSectionsCohomologyEquiv_equiv₀ X α e x
  rw [moduleSectionsCohomologyEquiv_apply] at he
  exact congrArg ((pushforwardSectionsIso p).hom.app (moduleAddSheaf Y G)) he

end AlgebraicGeometry.Scheme.Cohomology
