/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Basic

/-! # Original sections of a pushforward with compatible scalar actions -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
  (p : Y ⟶ X) (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤)) (σ : A →+* B)
  (hσ : p.appTop.hom.comp α = β.comp σ) (G : Y.Modules)

/-- The pushforward comparison is the identity on actual sections, with the
structural scalar action checked by the original compatible ring maps. -/
def modulePushforwardSectionsIso :
    moduleSectionsPresheaf X α ((Modules.pushforward p).obj G) ≅
      ((Opens.map p.base).op ⋙ moduleSectionsPresheaf Y β G) ⋙
        ModuleCat.restrictScalars σ := by
  let η := moduleSectionsMapAlong p α β σ hσ (𝟙 ((Modules.pushforward p).obj G))
  exact NatIso.ofComponents
    (fun U => (LinearEquiv.ofBijective (η.app U).hom
      (show Function.Bijective (fun x => x) from Function.bijective_id)).toModuleIso)
    (fun i => η.naturality i)

theorem modulePushforwardSectionsIso_hom_app_apply (U : X.Opensᵒᵖ)
    (m : (moduleSectionsPresheaf X α ((Modules.pushforward p).obj G)).obj U) :
    (modulePushforwardSectionsIso p α β σ hσ G).hom.app U m = m := rfl

theorem modulePushforwardSectionsIso_inv_app_apply (U : X.Opensᵒᵖ)
    (m : (((Opens.map p.base).op ⋙ moduleSectionsPresheaf Y β G) ⋙
      ModuleCat.restrictScalars σ).obj U) :
    (modulePushforwardSectionsIso p α β σ hσ G).inv.app U m = m := by
  have h := (modulePushforwardSectionsIso p α β σ hσ G).inv_hom_id_app U
  have he := congrArg (fun k => k m) h
  exact he

end AlgebraicGeometry.Scheme.Cohomology
