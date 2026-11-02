/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSectionsPostcomp
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.ForgetMaps

/-! # Postcomposition of the original affine-site section restriction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]
  {U V : S.AffineEtale} (g : V ⟶ U) (N : (Spec V.left.unop).Modules)
  (v : (Scheme.Modules.pullback V.hom).obj F ⟶ N)

/-- The native affine-test restriction and an arbitrary original coefficient
map obey the original section-unit equation before higher images enter. -/
theorem sectionsAddHom_affineTest_postcomp
    (x : (moduleSpecΓFunctor (R := U.left.unop)).obj
      ((Scheme.Modules.pullback U.hom).obj F)) :
    (moduleSpecΓFunctor (R := V.left.unop)).map v
      (sectionsAddHom S F
        ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g)) x) =
    (moduleSpecΓFunctor (R := V.left.unop)).map
      ((Scheme.Modules.pullbackComp (Spec.map g.left.unop) U.hom).hom.app F ≫
        (Scheme.Modules.pullbackCongr
          (MorphismProperty.Over.w ((Scheme.AffineEtale.Spec S).map g))).hom.app F ≫ v)
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g.left.unop)).unit.app
        ((Scheme.Modules.pullback U.hom).obj F)).app ⊤) x) := by
  have h := sectionsAddHom_affine_postcomp
    (R := U.left.unop) (T := V.left.unop) F U.hom V.hom g.left.unop
    (MorphismProperty.Over.w ((Scheme.AffineEtale.Spec S).map g)) N v x
  rw [← Scheme.EtaleAffineBasis.forget_spec_map g] at h
  convert h using 1

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
