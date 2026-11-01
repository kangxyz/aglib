/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionAdditive
public import Aglib.CategoryTheory.Sites.PresheafTransportValues

/-! # Original additive section values under geometric base restriction -/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.PresheafTransport
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]

/-- The actual base-restriction component is the original section comparison. -/
theorem additiveBaseRestrictionIso_hom_down (T : Over X)
    (s : ULift.{u + 1} Γ((pullback (T.hom ≫ f)).obj M, ⊤)) :
    (((additiveBaseRestrictionIso f M).hom.app (op T)) s).down =
      baseRestrictionSectionsAddEquiv f M T s.down := by
  unfold additiveBaseRestrictionIso
  exact liftTransportIsoOfTypeIso_hom_down
    (homPresheaf Y M) (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj M, ⊤))
    (sectionsEquiv Y M) (fun k => sectionsAddHom Y M k)
    (fun k s => sectionsAddHom_apply Y M k s)
    (homPresheaf X ((pullback f).obj M))
    (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj ((pullback f).obj M), ⊤))
    (sectionsEquiv X ((pullback f).obj M))
    (fun k => sectionsAddHom X ((pullback f).obj M) k)
    (fun k s => sectionsAddHom_apply X ((pullback f).obj M) k s)
    (Over.map f) (sectionsBaseRestrictionIso f M) (baseRestrictionSectionsAddEquiv f M)
    (fun T s => (baseRestrictionSectionsAddEquiv_apply f M T s).trans
      (sectionsBaseRestrictionIso_hom_apply f M T s).symm) T s

/-- Additive restriction has the unchanged section-presheaf value. -/
theorem additiveSectionsPresheaf_map_down {T U : Over Y} (g : U ⟶ T)
    (s : ULift.{u + 1} Γ((pullback T.hom).obj M, ⊤)) :
    ((additiveSectionsPresheaf Y M).map g.op s).down =
      (sectionsPresheaf Y M).map g.op s.down := by
  unfold additiveSectionsPresheaf
  rw [liftAdditiveTransport_map_apply]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
