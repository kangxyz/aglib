/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Cartesian
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/CartesianOpenBaseChange.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 194]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Original-map open base change on a specified cartesian square

The four original scheme maps determine the direct-image comparison. Its two mates retain
the original restriction and pullback adjunction units. The adjoint of a specified pullback
isomorphism becomes the literal local structure-module map under its constructed target comparison.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
include h
/-- A genuine cartesian square has the original inverse-image open range. -/
theorem opensRange_of_isPullback : a.opensRange = f ⁻¹ᵁ j.opensRange :=
  Scheme.Hom.opensRange_of_isPullback a b f j h
/-- The original restriction unit is invertible after this actual cartesian base change. -/
theorem isIso_cartesianOpenBaseChangeUnit :
    IsIso (Functor.whiskerRight (restrictAdjunction a).unit
      (pushforward f ⋙ restrictFunctor j)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro T
  change IsIso (M.presheaf.map (homOfLE (a.image_preimage_le (f ⁻¹ᵁ (j ''ᵁ T)))).op)
  have heq : a ''ᵁ (a ⁻¹ᵁ (f ⁻¹ᵁ (j ''ᵁ T))) = f ⁻¹ᵁ (j ''ᵁ T) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, opensRange_of_isPullback a b f j h]
    exact inf_eq_right.mpr (f.preimage_mono (j.image_le_opensRange T))
  have : IsIso (homOfLE (a.image_preimage_le (f ⁻¹ᵁ (j ''ᵁ T)))) := by
    convert (inferInstance : IsIso (eqToHom heq)) using 1
    exact Subsingleton.elim _ _
  infer_instance
/-- Open base change along the given cartesian square retains its original four scheme maps. -/
def cartesianOpenBaseChange :
    pushforward f ⋙ restrictFunctor j ≅ restrictFunctor a ⋙ pushforward b := by
  letI := isIso_cartesianOpenBaseChangeUnit a b f j h
  exact
    (Functor.leftUnitor _).symm ≪≫
    asIso (Functor.whiskerRight (restrictAdjunction a).unit
      (pushforward f ⋙ restrictFunctor j)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictFunctor a)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pushforwardComp a f) (restrictFunctor j) ≪≫
        Functor.isoWhiskerRight (pushforwardCongr h.w) (restrictFunctor j) ≪≫
        Functor.isoWhiskerRight (pushforwardComp b j).symm (restrictFunctor j) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (pushforward b) (restrictFunctorAdjCounitIso j) ≪≫
        Functor.rightUnitor _)
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The actual base-change map is the mate of the original pushforward square. -/
theorem cartesianOpenBaseChange_hom_mate :
    (cartesianOpenBaseChange a b f j h).hom =
      ((mateEquiv (restrictAdjunction a) (restrictAdjunction j)).symm
        (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom)).natTrans := by
  have hc : (restrictFunctorAdjCounitIso j).hom = (restrictAdjunction j).counit := rfl
  apply NatTrans.ext
  funext M
  simp [cartesianOpenBaseChange, cartesianPushforwardSquare, mateEquiv, Category.assoc, hc]
/-- The base-change map retains both original restriction adjunction units. -/
theorem cartesianOpenBaseChange_unit (M : U.Modules) :
    (pushforward f).map ((restrictAdjunction a).unit.app M) ≫
      (cartesianPushforwardSquare a b f j h).hom.app ((restrictFunctor a).obj M) =
    (restrictAdjunction j).unit.app ((pushforward f).obj M) ≫
      (pushforward j).map ((cartesianOpenBaseChange a b f j h).hom.app M) := by
  rw [cartesianOpenBaseChange_hom_mate]
  exact unit_mateEquiv_symm (restrictAdjunction a) (restrictAdjunction j)
    (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom) M
/-- The same map retains the original counits on the actual intersection module. -/
theorem cartesianOpenBaseChange_counit (M : W.Modules) :
    (restrictFunctor j).map ((cartesianPushforwardSquare a b f j h).hom.app M) ≫
      (restrictAdjunction j).counit.app ((pushforward b).obj M) =
    (cartesianOpenBaseChange a b f j h).hom.app ((pushforward a).obj M) ≫
      (pushforward b).map ((restrictAdjunction a).counit.app M) := by
  rw [cartesianOpenBaseChange_hom_mate]
  exact mateEquiv_counit_symm (restrictAdjunction a) (restrictAdjunction j)
    (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom) M
/-- Transposition of an original arrow after base change retains the original restriction unit. -/
theorem cartesianOpenBaseChange_homEquiv {E : X.Modules} {M : U.Modules}
    (q : E ⟶ (pushforward f).obj M) :
    (restrictAdjunction j).homEquiv _ _
      ((restrictFunctor j).map q ≫ (cartesianOpenBaseChange a b f j h).hom.app M) =
      q ≫ (pushforward f).map ((restrictAdjunction a).unit.app M) ≫
        (cartesianPushforwardSquare a b f j h).hom.app ((restrictFunctor a).obj M) := by
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_apply,
    ← cartesianOpenBaseChange_unit]
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The second mate retains the actual cartesian open base-change transformation. -/
def cartesianPullbackBaseChangeMate :
    restrictFunctor j ⋙ Scheme.Modules.pullback b ⟶
      Scheme.Modules.pullback f ⋙ restrictFunctor a :=
  (mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction b)).symm
    (cartesianOpenBaseChange a b f j h).hom
/-- The second mate is invertible by the original composite-adjunction comparison. -/
instance cartesianPullbackBaseChangeMate_isIso :
    IsIso (cartesianPullbackBaseChangeMate a b f j h) := by
  rw [cartesianPullbackBaseChangeMate, cartesianOpenBaseChange_hom_mate]
  rw [iterated_mateEquiv_conjugateEquiv_symm
    (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction b)
    (restrictAdjunction j) (restrictAdjunction a)]
  change IsIso ((conjugateEquiv
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction a))
    ((restrictAdjunction j).comp (pullbackPushforwardAdjunction b))).symm
      (cartesianPushforwardSquare a b f j h).hom)
  infer_instance
/-- Actual cartesian base change preserves the original pullback-adjunction unit. -/
theorem cartesianOpenBaseChange_pullback_unit (M : X.Modules) :
    (restrictFunctor j).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
      (cartesianOpenBaseChange a b f j h).hom.app ((Scheme.Modules.pullback f).obj M) =
    (pullbackPushforwardAdjunction b).unit.app ((restrictFunctor j).obj M) ≫
      (pushforward b).map ((cartesianPullbackBaseChangeMate a b f j h).app M) :=
  unit_mateEquiv_symm (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction b) (cartesianOpenBaseChange a b f j h).hom M
/-- The target comparison for the adjoint of an actual pullback isomorphism. -/
def cartesianAdjointTargetIso {E : X.Modules} {M : U.Modules}
    (e : (Scheme.Modules.pullback f).obj E ≅ M) :
    (restrictFunctor j).obj ((pushforward f).obj M) ≅
      (pushforward b).obj ((Scheme.Modules.pullback b).obj ((restrictFunctor j).obj E)) :=
  (cartesianOpenBaseChange a b f j h).app M ≪≫
    (pushforward b).mapIso ((restrictFunctor a).mapIso e.symm) ≪≫
    (pushforward b).mapIso ((asIso (cartesianPullbackBaseChangeMate a b f j h)).app E).symm
/-- The restricted original adjoint becomes literally the local adjunction unit. -/
theorem cartesianAdjointTargetIso_homEquiv {E : X.Modules} {M : U.Modules}
    (e : (Scheme.Modules.pullback f).obj E ≅ M) :
    (restrictFunctor j).map ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom) ≫
      (cartesianAdjointTargetIso a b f j h e).hom =
    (pullbackPushforwardAdjunction b).unit.app ((restrictFunctor j).obj E) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, cartesianAdjointTargetIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
  have hn := (cartesianOpenBaseChange a b f j h).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((restrictFunctor j).map ((pushforward f).map e.hom)), hn,
    Category.assoc]
  rw [← Category.assoc, cartesianOpenBaseChange_pullback_unit]
  simp [Category.assoc]
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The actual adjoint target is trivialized by the specified source chart trivialization. -/
def cartesianAdjointUnitTargetIso {E : X.Modules} {M : U.Modules}
    (e : (Scheme.Modules.pullback f).obj E ≅ M)
    (t : (restrictFunctor j).obj E ≅ SheafOfModules.unit V.ringCatSheaf) :
    (restrictFunctor j).obj ((pushforward f).obj M) ≅
      (pushforward b).obj (SheafOfModules.unit W.ringCatSheaf) :=
  cartesianAdjointTargetIso a b f j h e ≪≫
    (pushforward b).mapIso ((Scheme.Modules.pullback b).mapIso t ≪≫ pullbackUnitIso b)
/-- The original adjoint arrow becomes the original structure-module map on the chart. -/
theorem cartesianAdjointUnitTargetIso_homEquiv {E : X.Modules} {M : U.Modules}
    (e : (Scheme.Modules.pullback f).obj E ≅ M)
    (t : (restrictFunctor j).obj E ≅ SheafOfModules.unit V.ringCatSheaf) :
    (restrictFunctor j).map ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom) ≫
      (cartesianAdjointUnitTargetIso a b f j h e t).hom =
    t.hom ≫ SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom := by
  dsimp only [cartesianAdjointUnitTargetIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, cartesianAdjointTargetIso_homEquiv]
  rw [Functor.map_comp]
  have hn := (pullbackPushforwardAdjunction b).unit.naturality t.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  congr 1
  exact pullbackUnitIso_homEquiv b
end AlgebraicGeometry.Scheme.Modules
