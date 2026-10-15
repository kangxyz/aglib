/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/ProjectionFormulaOpenBaseChange.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 110]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Projection formula and open base change

The tensor pushforward and projection-formula maps commute with the original
cartesian open-base-change maps. The latter square retains the actual pullback
mate and both original open tensor comparison maps.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The original direct-image tensor map commutes with actual cartesian open base change. -/
theorem modulePushforwardTensorMap_openBaseChange (E M : U.Modules) :
    (tensorRestrictionIso j ((pushforward f).obj E) ((pushforward f).obj M)).hom ≫
      (restrictFunctor j).map (modulePushforwardTensorMap f E M) ≫
      (cartesianOpenBaseChange a b f j h).hom.app ((moduleTensorLeftFunctor U E).obj M) =
    (moduleTensorCoefficientMap V ((cartesianOpenBaseChange a b f j h).hom.app E)).app
        (((pushforward f).obj M).restrict j) ≫
      (moduleTensorLeftFunctor V ((pushforward b).obj (E.restrict a))).map
        ((cartesianOpenBaseChange a b f j h).hom.app M) ≫
      modulePushforwardTensorMap b (E.restrict a) (M.restrict a) ≫
      (pushforward b).map (tensorRestrictionIso a E M).hom := by
  apply moduleTensor_hom_ext
  intro T e m
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    restrictFunctor_map_app, Scheme.Modules.pushforward_map_app]
  let e' := ((cartesianOpenBaseChange a b f j h).hom.app E).app T e
  let m' := ((cartesianOpenBaseChange a b f j h).hom.app M).app T m
  erw [tensorRestrictionIso_section j ((pushforward f).obj E) ((pushforward f).obj M) T e m]
  erw [modulePushforwardTensorMap_section f E M (j ''ᵁ T) e m]
  erw [moduleTensorCoefficientMap_section
    ((cartesianOpenBaseChange a b f j h).hom.app E) (((pushforward f).obj M).restrict j) T e m]
  erw [moduleTensorLeftFunctor_map_section ((pushforward b).obj (E.restrict a))
    ((cartesianOpenBaseChange a b f j h).hom.app M) T e' m]
  erw [modulePushforwardTensorMap_section b (E.restrict a) (M.restrict a) T e' m']
  erw [tensorRestrictionIso_section a E M (b ⁻¹ᵁ T) e' m']
  dsimp only [e', m']
  rw [cartesianOpenBaseChange_hom_app, cartesianOpenBaseChange_hom_app,
    cartesianOpenBaseChange_hom_app]
  exact moduleTensorSection_restrict E M _ e m
end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The literal projection-formula arrow commutes with the original cartesian open
base change, original tensor restriction, and original adjunction mate. -/
theorem projectionFormulaMap_openBaseChange (E : X.Modules) (M : U.Modules) :
    (tensorRestrictionIso j E ((pushforward f).obj M)).hom ≫
      (restrictFunctor j).map (projectionFormulaMap f E M) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        ((moduleTensorLeftFunctor U ((Scheme.Modules.pullback f).obj E)).obj M) =
    (moduleTensorLeftFunctor V (E.restrict j)).map
        ((cartesianOpenBaseChange a b f j h).hom.app M) ≫
      projectionFormulaMap b (E.restrict j) (M.restrict a) ≫
      (pushforward b).map
        ((moduleTensorCoefficientMap W
          ((cartesianPullbackBaseChangeMate a b f j h).app E)).app (M.restrict a) ≫
          (tensorRestrictionIso a ((Scheme.Modules.pullback f).obj E) M).hom) := by
  apply moduleTensor_hom_ext
  intro T e m
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    restrictFunctor_map_app, Scheme.Modules.pushforward_map_app]
  let m' := ((cartesianOpenBaseChange a b f j h).hom.app M).app T m
  let e' := ((pullbackPushforwardAdjunction b).unit.app (E.restrict j)).app T e
  erw [tensorRestrictionIso_section j E ((pushforward f).obj M) T e m]
  erw [projectionFormulaMap_section f E M (j ''ᵁ T) e m]
  erw [moduleTensorLeftFunctor_map_section (E.restrict j)
    ((cartesianOpenBaseChange a b f j h).hom.app M) T e m]
  erw [projectionFormulaMap_section b (E.restrict j) (M.restrict a) T e m']
  erw [moduleTensorCoefficientMap_section
    ((cartesianPullbackBaseChangeMate a b f j h).app E) (M.restrict a) (b ⁻¹ᵁ T) e' m']
  erw [tensorRestrictionIso_section a ((Scheme.Modules.pullback f).obj E) M (b ⁻¹ᵁ T) _ m']
  rw [cartesianOpenBaseChange_hom_app]
  erw [moduleTensorSection_restrict ((Scheme.Modules.pullback f).obj E) M _ _ m]
  have hu := congrArg (fun k => k.app T e)
    (cartesianOpenBaseChange_pullback_unit a b f j h E)
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    restrictFunctor_map_app, Scheme.Modules.pushforward_map_app,
    cartesianOpenBaseChange_hom_app] at hu
  dsimp only [m', e']
  rw [cartesianOpenBaseChange_hom_app]
  exact congrArg (fun q => moduleTensorSection U ((Scheme.Modules.pullback f).obj E) M
    (a ''ᵁ (b ⁻¹ᵁ T)) q _) hu
end AlgebraicGeometry.Scheme.Modules
end
