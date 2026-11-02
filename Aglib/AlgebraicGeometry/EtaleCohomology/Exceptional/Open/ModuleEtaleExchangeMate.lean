/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleDirectImageSquareValued
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeComparison
public import Aglib.CategoryTheory.Adjunction.ExchangeTransport

/-! # The native chart exchange is the original adjunction mate -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- Evaluate the original two-comparison chain before substituting concrete
coefficient categories, keeping both actual comparison maps. -/
private theorem comparison_comp_hom_app
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    (P : A ⥤ B) (Q : B ⥤ C) (U : A ⥤ D) (V : B ⥤ E) (W : C ⥤ F)
    (P' : D ⥤ E) (Q' : E ⥤ F)
    (a : P ⋙ V ≅ U ⋙ P') (b : Q ⋙ W ≅ V ⋙ Q')
    (c : (P ⋙ Q) ⋙ W ≅ U ⋙ P' ⋙ Q')
    (hc : c = Functor.associator P Q W ≪≫ Functor.isoWhiskerLeft P b ≪≫
      (Functor.associator P V Q').symm ≪≫ Functor.isoWhiskerRight a Q' ≪≫
        Functor.associator U P' Q') (M : A) :
    c.hom.app M = b.hom.app (P.obj M) ≫ Q'.map (a.hom.app M) := by
  subst c
  simp

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

/-- The native alias has the two original factors of the shared constant-ring
comparison, with no replacement isomorphism or coefficient realization. -/
private theorem native_compRightIso_hom_app {X S T : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf T Λ) :
    (moduleDirectImageCompRightIso Λ f g).hom.app M =
      (moduleDirectImageComparison f Λ).hom.app ((moduleDirectImage g Λ).obj M) ≫
        (moduleValuedDirectImage f Λ).map ((moduleDirectImageComparison g Λ).hom.app M) :=
  comparison_comp_hom_app
    (moduleDirectImage g Λ) (moduleDirectImage f Λ)
    (moduleSheafEquivalence T Λ).inverse (moduleSheafEquivalence S Λ).inverse
    (moduleSheafEquivalence X Λ).inverse
    (moduleValuedDirectImage g Λ) (moduleValuedDirectImage f Λ)
    (moduleDirectImageComparison g Λ) (moduleDirectImageComparison f Λ)
    (moduleDirectImageCompRightIso Λ f g) rfl M

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  (Λ : Type (u + 1)) [Ring Λ]

/-- The chart exchange satisfies the original native horizontal-unit equation. -/
@[reassoc]
theorem moduleEtaleBaseChangeIso_horizontal_unit (M : ModuleSheaf X Λ) :
    (moduleDirectImage f Λ).map
        ((moduleInverseImageAdjunction (pullback.snd g f) Λ).unit.app M) ≫
      (moduleDirectImageSquareIso Λ f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).hom.app ((moduleInverseImage (pullback.snd g f) Λ).obj M) =
    (moduleInverseImageAdjunction g Λ).unit.app ((moduleDirectImage f Λ).obj M) ≫
      (moduleDirectImage g Λ).map ((moduleEtaleBaseChangeIso f g Λ).hom.app M) := by
  apply Adjunction.exchangeTransport_unit
    (moduleInverseImageAdjunction (pullback.snd g f) Λ)
    (moduleInverseImageAdjunction g Λ)
    (moduleValuedInverseImageAdjunction (pullback.snd g f) Λ)
    (moduleValuedInverseImageAdjunction g Λ)
    (moduleSheafEquivalence X Λ).inverse (moduleSheafEquivalence S Λ).inverse
    (moduleSheafEquivalence T Λ).inverse (moduleSheafEquivalence (pullback g f) Λ).inverse
    (moduleDirectImageComparison f Λ) (moduleDirectImageComparison (pullback.fst g f) Λ)
    (moduleDirectImageComparison (pullback.snd g f) Λ) (moduleDirectImageComparison g Λ)
    (moduleInverseImageValuedIso Λ (pullback.snd g f)) (moduleInverseImageValuedIso Λ g)
    (moduleDirectImageSquareIso Λ f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom
    (moduleValuedDirectImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition Λ).hom
    (moduleEtaleBaseChangeIso f g Λ).hom (moduleValuedEtaleBaseChangeIso f g Λ).hom
    (moduleInverseImageValuedIso_unit (pullback.snd g f) Λ)
    (moduleInverseImageValuedIso_unit g Λ) _
    (moduleEtaleBaseChangeIso_valued f g Λ)
    (moduleValuedEtaleBaseChangeIso_unit f g Λ) M
  intro N
  simpa only [native_compRightIso_hom_app, Category.assoc] using
    moduleDirectImageSquareIso_hom_valued Λ f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition N

/-- The genuine chart isomorphism is precisely the exchange of the original native adjunctions. -/
theorem moduleEtaleBaseChangeIso_hom :
    (moduleEtaleBaseChangeIso f g Λ).hom =
      moduleBaseChangeMap Λ f (pullback.fst g f) g (pullback.snd g f) pullback.condition := by
  apply NatTrans.ext
  funext M
  apply ((moduleInverseImageAdjunction g Λ).homEquiv _ _).injective
  exact (moduleEtaleBaseChangeIso_horizontal_unit f g Λ M).symm.trans
    (moduleBaseChangeMap_horizontal_unit Λ f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition M)

end AlgebraicGeometry.Scheme.EtaleCohomology
