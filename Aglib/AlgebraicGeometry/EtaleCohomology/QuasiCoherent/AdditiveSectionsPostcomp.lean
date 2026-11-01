/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Original affine section restriction followed by a module morphism -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

open Scheme.Modules

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]
  {R T : CommRingCat.{u}} (j : Spec R ⟶ S) (j' : Spec T ⟶ S)
  (φ : R ⟶ T) (h : Spec.map φ ≫ j = j')
  (N : (Spec T).Modules) (v : (Scheme.Modules.pullback j').obj F ⟶ N)

/-- Postcomposing the original affine section restriction retains the literal
pullback-composition map and original section unit. No cohomology or finite
presentation enters this equation. -/
theorem sectionsAddHom_affine_postcomp
    (x : (moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pullback j).obj F)) :
    (moduleSpecΓFunctor (R := T)).map v
      (sectionsAddHom S F
        (Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) h) x) =
    (moduleSpecΓFunctor (R := T)).map
      ((Scheme.Modules.pullbackComp (Spec.map φ) j).hom.app F ≫
        (Scheme.Modules.pullbackCongr h).hom.app F ≫ v)
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        ((Scheme.Modules.pullback j).obj F)).app ⊤) x) := by
  let t := (Scheme.Modules.pullbackComp (Spec.map φ) j).hom.app F ≫
    (Scheme.Modules.pullbackCongr h).hom.app F
  have hs := sectionsPresheaf_map_eq S F
    (Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) h) x
  change sectionsAddHom S F
    (Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) h) x = _ at hs
  have hs' := congrArg ((moduleSpecΓFunctor (R := T)).map v) hs
  have hm := ConcreteCategory.congr_hom
    ((moduleSpecΓFunctor (R := T)).map_comp t v)
    ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      ((Scheme.Modules.pullback j).obj F)).app ⊤) x)
  simpa only [t, Category.assoc] using hs'.trans hm.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
