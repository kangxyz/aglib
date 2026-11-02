/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.LocalizationPullback
public import Aglib.Algebra.Homology.ShortComplex.LocalizationPullback
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Complex
public import Aglib.Algebra.Homology.CochainComplexPlus.Single
public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-! # Whole termwise transport of original localization sequences -/
@[expose] public noncomputable section
namespace CategoryTheory
open Limits
variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  {J : A ⥤ B} {U : B ⥤ A} {V : B ⥤ C} {R : C ⥤ B}
  {J' : A' ⥤ B'} {U' : B' ⥤ A'} {V' : B' ⥤ C'} {R' : C' ⥤ B'}
  {F : B ⥤ B'} {G : A ⥤ A'} {H : C ⥤ C'} [J.Additive] [U.Additive] [V.Additive] [R.Additive]
  [J'.Additive] [U'.Additive] [V'.Additive] [R'.Additive]
  [F.Additive] [G.Additive] [H.Additive]
  (a : J ⊣ U) (a' : J' ⊣ U') (d : V ⊣ R) (d' : V' ⊣ R')
  (e : J ⋙ F ≅ G ⋙ J') (u : U ⋙ G ≅ F ⋙ U')
  (v : V ⋙ H ≅ F ⋙ V') (β : R ⋙ F ⟶ H ⋙ R')


/-- The actual first comparison as a natural iso. -/
def localizationPullbackFirstNatIso : (U ⋙ J) ⋙ F ≅ F ⋙ (U' ⋙ J') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight u _ ≪≫
    Functor.associator _ _ _

variable (h : LocalizationPullbackMateEquations a a' d d' e u v β)
  (z : ∀ M, a.counit.app M ≫ d.unit.app M = 0)
  (z' : ∀ M, a'.counit.app M ≫ d'.unit.app M = 0)
  (hS : ∀ M, ((ShortComplex.mk (a.counit.app M) (d.unit.app M) (z M)).map F).ShortExact)
  (hT : ∀ M, (ShortComplex.mk (a'.counit.app M) (d'.unit.app M) (z' M)).ShortExact)

/-- Exactness makes the original third exchange invertible naturally. -/
def localizationPullbackThirdNatIso : (V ⋙ R) ⋙ F ≅ F ⋙ (V' ⋙ R') := by
  let γ := compositeExchange β v
  have hγ (M : B) : IsIso (γ.app M) := by
    change IsIso ((compositeExchange β v).app M)
    rw [compositeExchange_app]
    exact inferInstanceAs (IsIso ((ShortComplex.π₃).mapIso
      (localizationSequencePullbackIso a a' d d' e u v β h M (z M)
        (z' (F.obj M)) (hS M) (hT (F.obj M)))).hom)
  letI : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact asIso γ

/-- Whole original counit/unit sequences transport termwise, without concrete carrier expansion. -/
def localizationSequenceComplexPullbackIso (K : CochainComplex.Plus B)
    (w : a.mapCochainComplexPlus.counit.app K ≫ d.mapCochainComplexPlus.unit.app K = 0)
    (w' : a'.mapCochainComplexPlus.counit.app (F.mapCochainComplexPlus.obj K) ≫
      d'.mapCochainComplexPlus.unit.app (F.mapCochainComplexPlus.obj K) = 0) :
    (ShortComplex.mk (a.mapCochainComplexPlus.counit.app K)
      (d.mapCochainComplexPlus.unit.app K) w).map F.mapCochainComplexPlus ≅
    ShortComplex.mk (a'.mapCochainComplexPlus.counit.app (F.mapCochainComplexPlus.obj K))
      (d'.mapCochainComplexPlus.unit.app (F.mapCochainComplexPlus.obj K)) w' := by
  refine ShortComplex.isoMk
    ((NatIso.mapCochainComplexPlus (localizationPullbackFirstNatIso e u)).app K)
    (Iso.refl _)
    ((NatIso.mapCochainComplexPlus
      (localizationPullbackThirdNatIso a a' d d' e u v β h z z' hS hT)).app K) ?_ ?_
  · apply ObjectProperty.hom_ext
    ext n : 1
    change (localizationPullbackFirstNatIso e u).hom.app (K.obj.X n) ≫
      a'.counit.app (F.obj (K.obj.X n)) = F.map (a.counit.app (K.obj.X n)) ≫ 𝟙 _
    simp only [localizationPullbackFirstNatIso, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    exact localizationPullback_counit a a' e u h.1 (K.obj.X n)
  · apply ObjectProperty.hom_ext
    ext n : 1
    change 𝟙 _ ≫ d'.unit.app (F.obj (K.obj.X n)) =
      F.map (d.unit.app (K.obj.X n)) ≫ (compositeExchange β v).app (K.obj.X n)
    rw [Category.id_comp, compositeExchange_app]
    exact (localizationPullback_unit d d' v β h.2 (K.obj.X n)).symm
end CategoryTheory
