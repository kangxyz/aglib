/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceDiagram
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.WholeNormalization
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualPasting

/-!
# Original native module exchange pasting

The native inverse-image comparisons define the actual whole comparison diagram.
Its associativity and equality-transport witnesses specialize the shared coherence
and mate-pasting suppliers, without replacing the original module functors.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original associativity comparison, without evaluating on any sheaf. -/
theorem moduleInverseImageComp_assoc_hom {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (moduleInverseImageCompIso Λ f (h ≫ g)).hom ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h).hom =
      (eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ)
        (Category.assoc h g f))).hom ≫
        (moduleInverseImageCompIso Λ (g ≫ f) h).hom ≫
        Functor.whiskerRight (moduleInverseImageCompIso Λ f g).hom (moduleInverseImage h Λ) ≫
        (Functor.associator (moduleInverseImage f Λ)
          (moduleInverseImage g Λ) (moduleInverseImage h Λ)).hom := by
  have hc := congrArg Iso.hom (moduleInverseImageCompIso_assoc Λ f g h)
  simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] using hc

/-- Equality transport in the second whole inverse-image composition comparison. -/
theorem moduleInverseImageComp_eqToHom_right_whole {X S T : Scheme.{u}}
    (f : S ⟶ X) {g g' : T ⟶ S} (e : g = g') :
    (moduleInverseImageCompIso Λ f g).hom ≫
        Functor.whiskerLeft (moduleInverseImage f Λ)
          (eqToHom (congrArg (fun k : T ⟶ S => moduleInverseImage k Λ) e)) =
      eqToHom (congrArg (fun k : T ⟶ X => moduleInverseImage k Λ)
        (congrArg (fun k => k ≫ f) e)) ≫ (moduleInverseImageCompIso Λ f g').hom := by
  subst g'
  simp

/-- Equality transport in the first whole inverse-image composition comparison. -/
theorem moduleInverseImageComp_eqToHom_left_whole {X S T : Scheme.{u}}
    {f f' : S ⟶ X} (e : f = f') (g : T ⟶ S) :
    (moduleInverseImageCompIso Λ f g).hom ≫
        Functor.whiskerRight
          (eqToHom (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) e))
          (moduleInverseImage g Λ) =
      eqToHom (congrArg (fun k : T ⟶ X => moduleInverseImage k Λ)
        (congrArg (fun k => g ≫ k) e)) ≫ (moduleInverseImageCompIso Λ f' g).hom := by
  subst f'
  simp

/-- Initial rotation of the actual whole associativity comparison. -/
theorem moduleInverseImageComp_assoc_start_whole {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (moduleInverseImageCompIso Λ (g ≫ f) h).hom ≫
        (Functor.whiskerRight (moduleInverseImageCompIso Λ f g).hom (moduleInverseImage h Λ) ≫
          (Functor.associator (moduleInverseImage f Λ)
          (moduleInverseImage g Λ) (moduleInverseImage h Λ)).hom) ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h).inv =
      (eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ)
        (Category.assoc h g f))).inv ≫ (moduleInverseImageCompIso Λ f (h ≫ g)).hom :=
  exchangeCoherence_rotate_start _ _ _ _ _ _ _
    (Iso.inv_hom_id _) (Iso.hom_inv_id (Functor.isoWhiskerLeft
      (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h)))
    (moduleInverseImageComp_assoc_hom Λ f g h).symm

/-- Terminal rotation of the actual whole associativity comparison. -/
theorem moduleInverseImageComp_assoc_finish_whole {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (moduleInverseImageCompIso Λ (g ≫ f) h).hom ≫
        Functor.whiskerRight (moduleInverseImageCompIso Λ f g).hom (moduleInverseImage h Λ) ≫
        (Functor.associator (moduleInverseImage f Λ)
          (moduleInverseImage g Λ) (moduleInverseImage h Λ)).hom =
      (eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ)
        (Category.assoc h g f))).inv ≫
        (moduleInverseImageCompIso Λ f (h ≫ g)).hom ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h).hom :=
  exchangeCoherence_rotate_finish _ _ _ _ (Iso.inv_hom_id _)
    (moduleInverseImageComp_assoc_hom Λ f g h).symm

section WholeHorizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- The actual whole comparison diagram; no coherence proof is part of its data. -/
def moduleInverseImageHorizontalDiagram :
    ExchangeCoherenceDiagram
      (ModuleSheaf S₀ Λ ⥤ ModuleSheaf X₂ Λ) where
  A := moduleInverseImage (f₂ ≫ (g₂ ≫ g₁)) Λ
  B := moduleInverseImage (g₂ ≫ g₁) Λ ⋙ moduleInverseImage f₂ Λ
  C₀ := moduleInverseImage g₁ Λ ⋙ moduleInverseImage g₂ Λ ⋙ moduleInverseImage f₂ Λ
  D := moduleInverseImage g₁ Λ ⋙ moduleInverseImage (f₂ ≫ g₂) Λ
  E := moduleInverseImage g₁ Λ ⋙ moduleInverseImage (h₂ ≫ f₁) Λ
  F := moduleInverseImage g₁ Λ ⋙ moduleInverseImage f₁ Λ ⋙ moduleInverseImage h₂ Λ
  G := moduleInverseImage (f₁ ≫ g₁) Λ ⋙ moduleInverseImage h₂ Λ
  H := moduleInverseImage (h₁ ≫ f₀) Λ ⋙ moduleInverseImage h₂ Λ
  I := moduleInverseImage f₀ Λ ⋙ moduleInverseImage h₁ Λ ⋙ moduleInverseImage h₂ Λ
  J := moduleInverseImage ((f₂ ≫ g₂) ≫ g₁) Λ
  K := moduleInverseImage ((h₂ ≫ f₁) ≫ g₁) Λ
  L := moduleInverseImage (h₂ ≫ (f₁ ≫ g₁)) Λ
  M := moduleInverseImage (h₂ ≫ (h₁ ≫ f₀)) Λ
  N := moduleInverseImage ((h₂ ≫ h₁) ≫ f₀) Λ
  O := moduleInverseImage f₀ Λ ⋙ moduleInverseImage (h₂ ≫ h₁) Λ
  p := (moduleInverseImageCompIso Λ (g₂ ≫ g₁) f₂).hom
  q := Functor.whiskerRight (moduleInverseImageCompIso Λ g₁ g₂).hom (moduleInverseImage f₂ Λ) ≫
    (Functor.associator (moduleInverseImage g₁ Λ)
      (moduleInverseImage g₂ Λ) (moduleInverseImage f₂ Λ)).hom
  b₀ := Functor.whiskerLeft (moduleInverseImage g₁ Λ) (moduleInverseImageCompIso Λ g₂ f₂).inv
  t₂ := Functor.whiskerLeft (moduleInverseImage g₁ Λ)
    (eqToIso (congrArg (fun k : X₂ ⟶ S₁ => moduleInverseImage k Λ) e₂)).hom
  c₀ := Functor.whiskerLeft (moduleInverseImage g₁ Λ) (moduleInverseImageCompIso Λ f₁ h₂).hom
  d := Functor.isoWhiskerRight (moduleInverseImageCompIso Λ g₁ f₁) (moduleInverseImage h₂ Λ) ≪≫
    Functor.associator (moduleInverseImage g₁ Λ) (moduleInverseImage f₁ Λ) (moduleInverseImage h₂ Λ)
  t₁ := Functor.whiskerRight
    (eqToIso (congrArg (fun k : X₁ ⟶ S₀ => moduleInverseImage k Λ) e₁)).hom
      (moduleInverseImage h₂ Λ)
  e₀ := Functor.whiskerRight (moduleInverseImageCompIso Λ f₀ h₁).hom (moduleInverseImage h₂ Λ) ≫
    (Functor.associator (moduleInverseImage f₀ Λ)
      (moduleInverseImage h₁ Λ) (moduleInverseImage h₂ Λ)).hom
  a := (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ)
    (Category.assoc f₂ g₂ g₁))).inv
  m := (moduleInverseImageCompIso Λ g₁ (f₂ ≫ g₂)).hom
  b := (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ)
    (congrArg (fun k : X₂ ⟶ S₁ => k ≫ g₁) e₂))).hom
  n := (moduleInverseImageCompIso Λ g₁ (h₂ ≫ f₁)).hom
  c := (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ)
    (Category.assoc h₂ f₁ g₁))).hom
  r := (moduleInverseImageCompIso Λ (f₁ ≫ g₁) h₂).hom
  e := (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ)
    (congrArg (fun k : X₁ ⟶ S₀ => h₂ ≫ k) e₁))).hom
  s := (moduleInverseImageCompIso Λ (h₁ ≫ f₀) h₂).hom
  z := (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ)
    (Category.assoc h₂ h₁ f₀))).inv
  u := (moduleInverseImageCompIso Λ f₀ (h₂ ≫ h₁)).hom
  v := Functor.whiskerLeft (moduleInverseImage f₀ Λ) (moduleInverseImageCompIso Λ h₁ h₂).hom
  τ := (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ) e)).hom

/-- The first actual whole comparison is the original associativity rotation. -/
theorem moduleInverseImageHorizontalDiagram_start :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).StartEquation :=
  moduleInverseImageComp_assoc_start_whole Λ g₁ g₂ f₂

/-- The second actual whole comparison is native equality transport. -/
theorem moduleInverseImageHorizontalDiagram_firstTransport :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).FirstTransportEquation :=
  moduleInverseImageComp_eqToHom_right_whole Λ g₁ e₂

/-- The middle actual whole comparison is the original associativity equation. -/
theorem moduleInverseImageHorizontalDiagram_middle :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).MiddleEquation :=
  moduleInverseImageComp_assoc_hom Λ g₁ f₁ h₂

/-- The fourth actual whole comparison is native equality transport. -/
theorem moduleInverseImageHorizontalDiagram_secondTransport :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).SecondTransportEquation :=
  moduleInverseImageComp_eqToHom_left_whole Λ e₁ h₂

/-- The final actual whole comparison is the original associativity rotation. -/
theorem moduleInverseImageHorizontalDiagram_finish :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).FinishEquation :=
  moduleInverseImageComp_assoc_finish_whole Λ f₀ h₁ h₂

/-- Source equalities close the actual whole transport pentagon. -/
theorem moduleInverseImageHorizontalDiagram_transport :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).TransportEquation := by
  dsimp only [ExchangeCoherenceDiagram.TransportEquation, moduleInverseImageHorizontalDiagram]
  exact exchangeCoherence_whole_transport
    (C := ModuleSheaf S₀ Λ ⥤ ModuleSheaf X₂ Λ)
    (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ)
    (Category.assoc f₂ g₂ g₁)
    (congrArg (fun k : X₂ ⟶ S₁ => k ≫ g₁) e₂)
    (Category.assoc h₂ f₁ g₁)
    (congrArg (fun k : X₁ ⟶ S₀ => h₂ ≫ k) e₁)
    (Category.assoc h₂ h₁ f₀) e

/-- The whole actual comparison chase consumes only its named native witnesses. -/
theorem moduleInverseImageHorizontalDiagram_chain :
    (moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).ChainEquation :=
  ExchangeCoherenceDiagram.chain _
    (moduleInverseImageHorizontalDiagram_start Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (moduleInverseImageHorizontalDiagram_firstTransport Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (moduleInverseImageHorizontalDiagram_middle Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (moduleInverseImageHorizontalDiagram_secondTransport Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (moduleInverseImageHorizontalDiagram_finish Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (moduleInverseImageHorizontalDiagram_transport Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

/-- Evaluate the proved whole diagram; no concrete comparison proof is repeated. -/
theorem moduleInverseImageHorizontalDiagram_chain_app (A : ModuleSheaf S₀ Λ) :
    ((moduleInverseImageHorizontalDiagram Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).app A).ChainEquation :=
  ExchangeCoherenceDiagram.chain_app _
    (moduleInverseImageHorizontalDiagram_chain Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) A

/-- The proved whole diagram has the shared whiskering recipe used by extraction. -/
theorem moduleInverseImageHorizontalDiagram_whiskered :
    WhiskeredComparisonChainEquation
    (moduleInverseImageCompIso Λ g₁ g₂) (moduleInverseImageCompIso Λ g₁ f₁)
    (moduleInverseImageCompIso Λ f₀ h₁)
    (moduleInverseImageCompIso Λ (g₂ ≫ g₁) f₂).hom
    (Functor.whiskerLeft (moduleInverseImage g₁ Λ) (moduleInverseImageCompIso Λ g₂ f₂).inv)
    (Functor.whiskerLeft (moduleInverseImage g₁ Λ)
      (eqToIso (congrArg (fun k : X₂ ⟶ S₁ => moduleInverseImage k Λ) e₂)).hom)
    (Functor.whiskerLeft (moduleInverseImage g₁ Λ) (moduleInverseImageCompIso Λ f₁ h₂).hom)
    (Functor.whiskerRight
      (eqToIso (congrArg (fun k : X₁ ⟶ S₀ => moduleInverseImage k Λ) e₁)).hom
      (moduleInverseImage h₂ Λ))
    (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ) e)).hom
    (moduleInverseImageCompIso Λ f₀ (h₂ ≫ h₁)).hom
    (Functor.whiskerLeft (moduleInverseImage f₀ Λ) (moduleInverseImageCompIso Λ h₁ h₂).hom) :=
  moduleInverseImageHorizontalDiagram_chain Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e


end WholeHorizontal

/-- The canonical whole natural-iso factorization of the actual inverse-image square. -/
theorem moduleInverseImageSquareIso_eq_comp {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    moduleInverseImageSquareIso Λ f f' g g' h =
      (moduleInverseImageCompIso Λ g f').symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage k Λ) h) ≪≫
        moduleInverseImageCompIso Λ f g' := rfl

/-- The original underived exchange remains an explicit native mate. -/
theorem moduleBaseChangeMap_eq_nativeMate {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    moduleBaseChangeMap Λ f f' g g' h =
      (mateEquiv (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
        (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)).natTrans := rfl

section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Actual horizontal square coherence is proved in the whole functor category. -/
theorem moduleInverseImageSquareIso_hComp_whole :
    WholeHorizontalSquareEquation
      (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom
      (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom
      (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom
      (moduleInverseImageCompIso Λ g₁ g₂).hom (moduleInverseImageCompIso Λ h₁ h₂).hom :=
  exchangeCoherence_normalize_whole
    (moduleInverseImageCompIso Λ g₁ g₂) (moduleInverseImageCompIso Λ h₁ h₂)
    (moduleInverseImageCompIso Λ (g₂ ≫ g₁) f₂) (moduleInverseImageCompIso Λ g₂ f₂)
    (eqToIso (congrArg (fun k : X₂ ⟶ S₁ => moduleInverseImage k Λ) e₂))
    (moduleInverseImageCompIso Λ f₁ h₂)
    (moduleInverseImageCompIso Λ g₁ f₁)
    (eqToIso (congrArg (fun k : X₁ ⟶ S₀ => moduleInverseImage k Λ) e₁))
    (moduleInverseImageCompIso Λ f₀ h₁)
    (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => moduleInverseImage k Λ) e))
    (moduleInverseImageCompIso Λ f₀ (h₂ ≫ h₁))
    (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁)
    (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂)
    (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (moduleInverseImageSquareIso_eq_comp Λ f₀ f₁ g₁ h₁ e₁)
    (moduleInverseImageSquareIso_eq_comp Λ f₁ f₂ g₂ h₂ e₂)
    (moduleInverseImageSquareIso_eq_comp Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (moduleInverseImageHorizontalDiagram_whiskered Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

/-- Evaluate only the final actual horizontal square, not its internal long chase. -/
theorem moduleInverseImageSquareIso_hComp (A : ModuleSheaf S₀ Λ) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleInverseImageCompIso Λ g₁ g₂).hom (moduleInverseImageCompIso Λ h₁ h₂).hom A :=
  wholeHorizontalSquare_app
    (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom
    (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom
    (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom
    (moduleInverseImageCompIso Λ g₁ g₂).hom (moduleInverseImageCompIso Λ h₁ h₂).hom
    (moduleInverseImageSquareIso_hComp_whole Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) A

/-- Horizontal pasting for the actual underived exchange maps, with native comparisons. -/
theorem moduleBaseChangeMap_hComp (K : ModuleSheaf X₀ Λ) :
    (moduleInverseImageCompIso Λ g₁ g₂).hom.app ((moduleDirectImage f₀ Λ).obj K) ≫
        (moduleInverseImage g₂ Λ).map ((moduleBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁).app K) ≫
        (moduleBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂).app ((moduleInverseImage h₁ Λ).obj K) =
      (moduleBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).app K ≫
        (moduleDirectImage f₂ Λ).map ((moduleInverseImageCompIso Λ h₁ h₂).hom.app K) := by
  apply actualHorizontalMateEquation_eq
    (moduleBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂)
    (moduleBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (moduleInverseImageCompIso Λ g₁ g₂).hom (moduleInverseImageCompIso Λ h₁ h₂).hom K
  exact actualHorizontalMateEquation_of_mates
    (moduleInverseImageAdjunction f₀ Λ) (moduleInverseImageAdjunction f₁ Λ)
      (moduleInverseImageAdjunction f₂ Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
    (moduleInverseImageCompIso Λ g₁ g₂).hom (moduleInverseImageCompIso Λ h₁ h₂).hom
    (moduleBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂)
    (moduleBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (moduleBaseChangeMap_eq_nativeMate Λ f₀ f₁ g₁ h₁ e₁)
    (moduleBaseChangeMap_eq_nativeMate Λ f₁ f₂ g₂ h₂ e₂)
    (moduleBaseChangeMap_eq_nativeMate Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e) K
    (horizontalMateEquation _ _ _ _ _
      (moduleInverseImageAdjunction f₀ Λ) (moduleInverseImageAdjunction f₁ Λ)
      (moduleInverseImageAdjunction f₂ Λ)
      (moduleInverseImageSquareIso_hComp Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K)

end Horizontal

/-- Transposing the commuting square inverts its canonical inverse-image comparison. -/
theorem moduleInverseImageSquareIso_transpose {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    moduleInverseImageSquareIso Λ g g' f f' e.symm =
      (moduleInverseImageSquareIso Λ f f' g g' e).symm := by
  simp only [moduleInverseImageSquareIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

/-- The vertical square-coherence law follows from transposed horizontal coherence. -/
theorem moduleInverseImageSquareIso_vComp {S X Y S' X' Y' : Scheme.{u}}
    (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
    (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
    (ef : f' ≫ g = g' ≫ f) (ek : k' ≫ g' = g'' ≫ k)
    (e : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (A : ModuleSheaf S Λ) :
    (moduleInverseImageCompIso Λ f' k').hom.app ((moduleInverseImage g Λ).obj A) ≫
        (moduleInverseImage k' Λ).map ((moduleInverseImageSquareIso Λ f f' g g' ef).hom.app A) ≫
        (moduleInverseImageSquareIso Λ k k' g' g'' ek).hom.app ((moduleInverseImage f Λ).obj A) =
      (moduleInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).hom.app A ≫
        (moduleInverseImage g'' Λ).map ((moduleInverseImageCompIso Λ f k).hom.app A) := by
  have hp := moduleInverseImageSquareIso_hComp Λ g g' g'' f k f' k' ef.symm ek.symm e.symm A
  dsimp only [HorizontalSquareEquation, TwoSquare.mk, TwoSquare.natTrans] at hp
  rw [moduleInverseImageSquareIso_transpose Λ f f' g g' ef,
    moduleInverseImageSquareIso_transpose Λ k k' g' g'' ek,
    moduleInverseImageSquareIso_transpose Λ (k ≫ f) (k' ≫ f') g g'' e] at hp
  have hr := congrArg (fun z =>
    (moduleInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).hom.app A ≫ z ≫
      (moduleInverseImage k' Λ).map ((moduleInverseImageSquareIso Λ f f' g g' ef).hom.app A) ≫
      (moduleInverseImageSquareIso Λ k k' g' g'' ek).hom.app ((moduleInverseImage f Λ).obj A)) hp
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app] at hr
  rw [(moduleInverseImage k' Λ).map_id
    ((moduleInverseImage f Λ ⋙ moduleInverseImage g' Λ).obj A)] at hr
  simpa only [CategoryTheory.Functor.comp_obj, CategoryTheory.Category.id_comp,
    Iso.inv_hom_id_app, CategoryTheory.Category.comp_id] using hr.symm

section VerticalPasting
variable {S X Y S' X' Y' : Scheme.{u}}
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))

/-- Actual vertical underived exchange pasting, normalized by the native comparisons. -/
theorem moduleBaseChangeMap_vComp_mate
    (K : ModuleSheaf Y Λ) :
    VerticalMateEquation
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ k k' g' g'' h₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
      (moduleDirectImageCompIso Λ f k) (moduleDirectImageCompIso Λ f' k')
      (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
      (moduleInverseImageAdjunction k Λ) (moduleInverseImageAdjunction k' Λ)
      (moduleInverseImageAdjunction (k ≫ f) Λ) (moduleInverseImageAdjunction (k' ≫ f') Λ) K :=
  verticalMateEquation
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _
      (moduleInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
    (moduleInverseImageCompIso Λ f k) (moduleInverseImageCompIso Λ f' k')
    (moduleDirectImageCompIso Λ f k) (moduleDirectImageCompIso Λ f' k')
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (moduleInverseImageAdjunction k Λ) (moduleInverseImageAdjunction k' Λ)
    (moduleInverseImageAdjunction (k ≫ f) Λ) (moduleInverseImageAdjunction (k' ≫ f') Λ)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f k)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f' k')
    (moduleInverseImageSquareIso_vComp Λ f k f' k' g g' g'' h₁ h₂ h) K

/-- Vertical pasting of the actual exchange maps under the native direct-image comparisons. -/
theorem moduleBaseChangeMap_vComp (K : ModuleSheaf Y Λ) :
    (moduleInverseImage g Λ).map ((moduleDirectImageCompIso Λ f k).hom.app K) ≫
        (moduleBaseChangeMap Λ f f' g g' h₁).app ((moduleDirectImage k Λ).obj K) ≫
        (moduleDirectImage f' Λ).map ((moduleBaseChangeMap Λ k k' g' g'' h₂).app K) =
      (moduleBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h).app K ≫
        (moduleDirectImageCompIso Λ f' k').hom.app ((moduleInverseImage g'' Λ).obj K) := by
  apply actualVerticalMateEquation_eq
    (moduleBaseChangeMap Λ f f' g g' h₁) (moduleBaseChangeMap Λ k k' g' g'' h₂)
    (moduleBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h)
    (moduleDirectImageCompIso Λ f k).hom (moduleDirectImageCompIso Λ f' k').hom K
  exact actualVerticalMateEquation_of_mates
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (moduleInverseImageAdjunction k Λ) (moduleInverseImageAdjunction k' Λ)
    (moduleInverseImageAdjunction (k ≫ f) Λ) (moduleInverseImageAdjunction (k' ≫ f') Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
    (moduleDirectImageCompIso Λ f k) (moduleDirectImageCompIso Λ f' k')
    (moduleBaseChangeMap Λ f f' g g' h₁) (moduleBaseChangeMap Λ k k' g' g'' h₂)
    (moduleBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h)
    (moduleBaseChangeMap_eq_nativeMate Λ f f' g g' h₁)
    (moduleBaseChangeMap_eq_nativeMate Λ k k' g' g'' h₂)
    (moduleBaseChangeMap_eq_nativeMate Λ (k ≫ f) (k' ≫ f') g g'' h) K
    (moduleBaseChangeMap_vComp_mate Λ f k f' k' g g' g'' h₁ h₂ h K)

end VerticalPasting

end AlgebraicGeometry.Scheme.EtaleCohomology
