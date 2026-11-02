/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.LocalizationPullback
public import Aglib.Algebra.Homology.ShortComplex.ThirdIso

/-! # Whole original localization sequences under actual adjunction comparisons -/
@[expose] public noncomputable section
namespace CategoryTheory
open Limits
variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  [Preadditive B] [Preadditive B'] [Balanced B']
  {J : A ⥤ B} {U : B ⥤ A} {V : B ⥤ C} {R : C ⥤ B}
  {J' : A' ⥤ B'} {U' : B' ⥤ A'} {V' : B' ⥤ C'} {R' : C' ⥤ B'}
  {F : B ⥤ B'} {G : A ⥤ A'} {H : C ⥤ C'} [F.PreservesZeroMorphisms]
  (a : J ⊣ U) (a' : J' ⊣ U') (d : V ⊣ R) (d' : V' ⊣ R')
  (e : J ⋙ F ≅ G ⋙ J') (u : U ⋙ G ≅ F ⋙ U')
  (v : V ⋙ H ≅ F ⋙ V') (β : R ⋙ F ⟶ H ⋙ R')

/-- Actual first-vertex comparison, with no choice of a replacement map. -/
def localizationPullbackFirstIso (M : B) :
    F.obj (J.obj (U.obj M)) ≅ J'.obj (U'.obj (F.obj M)) :=
  e.app (U.obj M) ≪≫ J'.mapIso (u.app M)

/-- Actual third-vertex comparison, before its invertibility is proved. -/
def localizationPullbackThirdMap (M : B) :
    F.obj (R.obj (V.obj M)) ⟶ R'.obj (V'.obj (F.obj M)) :=
  β.app (V.obj M) ≫ R'.map (v.hom.app M)

/-- A whole original adjunction-square predicate used by sequence/complex consumers. -/
def LocalizationPullbackMateEquations : Prop :=
  mateEquiv a a' (TwoSquare.mk _ _ _ _ e.inv) = TwoSquare.mk _ _ _ _ u.hom ∧
    (mateEquiv d d' (TwoSquare.mk _ _ _ _ v.inv)).natTrans = β

/-- The complete sequence map is assembled before specializing concrete sheaf carriers. -/
def localizationSequencePullbackMap
    (h : LocalizationPullbackMateEquations a a' d d' e u v β) (M : B)
    (z : a.counit.app M ≫ d.unit.app M = 0)
    (z' : a'.counit.app (F.obj M) ≫ d'.unit.app (F.obj M) = 0) :
    (ShortComplex.mk (a.counit.app M) (d.unit.app M) z).map F ⟶
      ShortComplex.mk (a'.counit.app (F.obj M)) (d'.unit.app (F.obj M)) z' :=
  ShortComplex.homMk (localizationPullbackFirstIso e u M).hom
    (𝟙 _) (localizationPullbackThirdMap v β M)
    ((localizationPullback_counit a a' e u h.1 M).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (localizationPullback_unit d d' v β h.2 M).symm)

/-- Exactness forces invertibility of the actual closed mate on the localization vertex. -/
def localizationSequencePullbackIso
    (h : LocalizationPullbackMateEquations a a' d d' e u v β) (M : B)
    (z : a.counit.app M ≫ d.unit.app M = 0)
    (z' : a'.counit.app (F.obj M) ≫ d'.unit.app (F.obj M) = 0)
    (hS : ((ShortComplex.mk (a.counit.app M) (d.unit.app M) z).map F).ShortExact)
    (hT : (ShortComplex.mk (a'.counit.app (F.obj M)) (d'.unit.app (F.obj M)) z').ShortExact) :
    (ShortComplex.mk (a.counit.app M) (d.unit.app M) z).map F ≅
      ShortComplex.mk (a'.counit.app (F.obj M)) (d'.unit.app (F.obj M)) z' := by
  let φ := localizationSequencePullbackMap a a' d d' e u v β h M z z'
  haveI : IsIso φ.τ₁ := inferInstanceAs (IsIso (localizationPullbackFirstIso e u M).hom)
  haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (F.obj M)))
  haveI : IsIso φ.τ₃ := ShortComplex.isIso₃_of_shortExact_of_isIso₁₂ φ hS hT
  haveI := ShortComplex.isIso_of_isIso φ
  exact asIso φ
end CategoryTheory
