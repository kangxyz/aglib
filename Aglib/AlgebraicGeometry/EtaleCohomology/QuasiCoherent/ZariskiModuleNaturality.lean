/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiModules

/-! # Native open-chart restriction on quasi-coherent sections -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Transporting a pullback section through the native open comparison gives the
original restriction-adjunction unit, not a new section map. -/
theorem nativeSectionPullback_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((restrictFunctorIsoPullback f).inv.app M) ⊤
        (nativeSectionPullback f M s) =
      Scheme.Modules.Hom.app ((restrictAdjunction f).unit.app M) ⊤ s := by
  rw [nativeSectionPullback_eq_unit]
  exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤ s)
    (restrictFunctorIsoPullback_inv_adjunction_unit f M)

/-- Original over-site restrictions on open immersions agree with native module restriction,
including the original composition and equality comparisons. -/
theorem openOverSections_naturality (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    {T U : Over X} (f : U ⟶ T) [IsOpenImmersion T.hom] [IsOpenImmersion U.hom]
    [IsOpenImmersion f.left] (s : Γ((pullback T.hom).obj F, ⊤)) :
    Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.hom).inv.app F) ⊤
        ((sectionsPresheaf X F).map f.op s) =
      Scheme.Modules.Hom.app
        ((restrictFunctorComp f.left T.hom).inv.app F ≫
          (restrictFunctorCongr (Over.w f)).hom.app F) ⊤
        (Scheme.Modules.Hom.app ((restrictAdjunction f.left).unit.app (F.restrict T.hom)) ⊤
          (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback T.hom).inv.app F) ⊤ s)) := by
  have h : ((pullbackComp f.left T.hom).hom.app F ≫
        (pullbackCongr (Over.w f)).hom.app F) ≫
          (restrictFunctorIsoPullback U.hom).inv.app F =
      (pullback f.left).map ((restrictFunctorIsoPullback T.hom).inv.app F) ≫
        (restrictFunctorIsoPullback f.left).inv.app (F.restrict T.hom) ≫
          (restrictFunctorComp f.left T.hom).inv.app F ≫
            (restrictFunctorCongr (Over.w f)).hom.app F := by
    rw [Category.assoc, restrictPullback_congr_inv, ← Category.assoc,
      restrictPullback_comp_inv]
    rw [← Category.assoc, ← (restrictFunctorIsoPullback f.left).inv.naturality]
    simp only [Category.assoc]
  have he := congrArg (fun k => Scheme.Modules.Hom.app k ⊤
    (nativeSectionPullback f.left ((pullback T.hom).obj F) s)) h
  rw [sectionsPresheaf_map_eq, ← nativeSectionPullback_eq_unit]
  change _ = Scheme.Modules.Hom.app
    ((restrictFunctorComp f.left T.hom).inv.app F ≫
      (restrictFunctorCongr (Over.w f)).hom.app F) ⊤
    (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback f.left).inv.app (F.restrict T.hom)) ⊤
      (Scheme.Modules.Hom.app ((pullback f.left).map
        ((restrictFunctorIsoPullback T.hom).inv.app F)) ⊤
        (nativeSectionPullback f.left ((pullback T.hom).obj F) s))) at he
  rw [nativeSectionPullback_naturality, nativeSectionPullback_restrict] at he
  exact he

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
