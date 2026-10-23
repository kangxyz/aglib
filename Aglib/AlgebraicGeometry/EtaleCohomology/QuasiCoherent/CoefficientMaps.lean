/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionScalars

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveTransport

/-! # Native coefficient maps on quasi-coherent étale sections -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The actual pullback-section restrictions commute with native coefficient maps. -/
theorem sectionsPresheaf_coefficient_naturality (g : F ⟶ G) {T U : Over X} (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj F, ⊤)) :
    Scheme.Modules.Hom.app ((pullback U.hom).map g) ⊤
        ((sectionsPresheaf X F).map f.op s) =
      (sectionsPresheaf X G).map f.op
        (Scheme.Modules.Hom.app ((pullback T.hom).map g) ⊤ s) := by
  rw [sectionsPresheaf_map_eq, sectionsPresheaf_map_eq,
    ← nativeSectionPullback_eq_unit, ← nativeSectionPullback_eq_unit]
  have h := congrArg
    (fun q => Scheme.Modules.Hom.app q ⊤
      (nativeSectionPullback f.left ((pullback T.hom).obj F) s))
    (((pullbackComp f.left T.hom) ≪≫ (pullbackCongr (Over.w f))).hom.naturality g)
  change Scheme.Modules.Hom.app
      ((pullbackComp f.left T.hom).hom.app G ≫
        (pullbackCongr (Over.w f)).hom.app G) ⊤
      (Scheme.Modules.Hom.app ((pullback f.left).map ((pullback T.hom).map g)) ⊤
        (nativeSectionPullback f.left ((pullback T.hom).obj F) s)) = _ at h
  rw [nativeSectionPullback_naturality] at h
  exact h.symm

/-- The original coefficient section map on explicit native carriers. -/
def coefficientSectionsAddHom (g : F ⟶ G) (T : Over X) :
    Γ((pullback T.hom).obj F, ⊤) →+ Γ((pullback T.hom).obj G, ⊤) :=
  (Scheme.Modules.Hom.app ((pullback T.hom).map g) ⊤).hom

/-- Bundling the original restriction does not change coefficient naturality. -/
theorem sectionsAddHom_coefficient_naturality (g : F ⟶ G) {T U : Over X} (f : U ⟶ T)
    (s : Γ((pullback T.hom).obj F, ⊤)) :
    coefficientSectionsAddHom X g U (sectionsAddHom X F f s) =
      sectionsAddHom X G f (coefficientSectionsAddHom X g T s) :=
  sectionsPresheaf_coefficient_naturality X g f s

/-- A native module morphism on the original big over-site sections. -/
def additiveSectionsMap (g : F ⟶ G) :
    additiveSectionsPresheaf X F ⟶ additiveSectionsPresheaf X G :=
  liftTransportHomSame (homPresheaf X F)
      (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj F, ⊤))
      (sectionsEquiv X F) (fun f => sectionsAddHom X F f)
      (fun f s => sectionsAddHom_apply X F f s)
      (homPresheaf X G)
      (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj G, ⊤))
      (sectionsEquiv X G) (fun f => sectionsAddHom X G f)
      (fun f s => sectionsAddHom_apply X G f s)
      (coefficientSectionsAddHom X g)
      (fun f s => sectionsAddHom_coefficient_naturality X g f s)

/-- A native module morphism induces the original pointwise section map on coefficients. -/
def additiveCoefficientMap (g : F ⟶ G) : additiveCoefficient X F ⟶ additiveCoefficient X G where
  hom := Functor.whiskerLeft (Scheme.Etale.forget X).op (additiveSectionsMap X g)

/-- Taking `down` of a coefficient map retains the original geometric module map. -/
@[simp]
theorem additiveCoefficientMap_down (g : F ⟶ G) (T : X.Etale)
    (s : (additiveCoefficient X F).obj.obj (op T)) :
    (((additiveCoefficientMap X g).hom.app (op T)) s).down =
      Scheme.Modules.Hom.app ((pullback T.hom).map g) ⊤ s.down := rfl

/-- The coefficient construction preserves the original identity morphism. -/
@[simp]
theorem additiveCoefficientMap_id : additiveCoefficientMap X (𝟙 F) = 𝟙 _ := by
  ext T s
  apply ULift.ext
  change (((additiveCoefficientMap X (𝟙 F)).hom.app (op T.unop)) s).down = s.down
  rw [additiveCoefficientMap_down, CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
  rfl

/-- The coefficient construction preserves the original composition. -/
@[simp]
theorem additiveCoefficientMap_comp {H : X.Modules} [H.IsQuasicoherent]
    (g : F ⟶ G) (h : G ⟶ H) :
    additiveCoefficientMap X (g ≫ h) =
      additiveCoefficientMap X g ≫ additiveCoefficientMap X h := by
  ext T s
  apply ULift.ext
  change (((additiveCoefficientMap X (g ≫ h)).hom.app (op T.unop)) s).down =
    (((additiveCoefficientMap X h).hom.app (op T.unop))
      (((additiveCoefficientMap X g).hom.app (op T.unop)) s)).down
  rw [additiveCoefficientMap_down, additiveCoefficientMap_down, additiveCoefficientMap_down,
    CategoryTheory.Functor.map_comp, Scheme.Modules.Hom.comp_app]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
