/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageSourceTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePasting
public import Aglib.CategoryTheory.NatTrans.IdentityBasePastingFactor

/-! # The original ordinary-image mate for the given Cartesian square -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
private theorem exchange_identity_transport
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D) (β : F ⋙ G ⟶ H ⋙ I) :
    Functor.whiskerLeft F (𝟙 G) ≫ β = β ≫ Functor.whiskerRight (𝟙 H) I := by
  ext K
  exact (Category.id_comp (β.app K)).trans
    ((congrArg (fun t => β.app K ≫ t) (I.map_id (H.obj K))).trans
      (Category.comp_id (β.app K))).symm

universe u wX wS wX' wT wL

section Transport
variable (Λ : Type (u + 1)) [Ring Λ] {X S X' T : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Equality transport of the original square changes neither of its actual mates. -/
theorem moduleUnboundedDerivedBaseChangeMap_transport
    (f : X ⟶ S) (f' : X' ⟶ T) (g₀ g : T ⟶ S) (a₀ a : X' ⟶ X)
    (hg : g₀ = g) (ha : a₀ = a)
    (h₀ : f' ≫ g₀ = a₀ ≫ f) (h : f' ≫ g = a ≫ f) :
    Functor.whiskerLeft (moduleUnboundedDerivedDirectImage Λ f)
        (eqToIso (congrArg (fun k : T ⟶ S => moduleUnboundedDerivedInverseImage Λ k) hg)).hom ≫
        moduleUnboundedDerivedBaseChangeMap Λ f f' g a h =
      moduleUnboundedDerivedBaseChangeMap Λ f f' g₀ a₀ h₀ ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun k : X' ⟶ X => moduleUnboundedDerivedInverseImage Λ k) ha)).hom
          (moduleUnboundedDerivedDirectImage Λ f') := by
  subst g₀
  subst a₀
  simp only [eqToIso_refl, Iso.refl_hom]
  exact exchange_identity_transport _ _ _ _ (moduleUnboundedDerivedBaseChangeMap Λ f f' g a h)
end Transport

variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (g : T ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback g f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]

/-- Literal β, actual source-only β and the inverse source compositor equal the original
mate of the given square. This is a pasting equality, not an inference from invertibility. -/
theorem moduleUnboundedDerivedBaseChangeMap_cartesian_factor :
    CartesianSourceTargetFactorEquation
      (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition)
      (moduleUnboundedDirectImageSourceTransport (pullback.fst g f) f'
        sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ)
      (moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ)
      (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  let e := sq.flip.isoPullback
  have ht : f' ≫ (𝟙 T ≫ g) = (e.hom ≫ pullback.snd g f) ≫ f := by
    rw [Category.id_comp, sq.flip.isoPullback_hom_snd]
    exact sq.w.symm
  apply identityBasePasting_factor
    (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition)
    (moduleUnboundedDerivedBaseChangeMap Λ (pullback.fst g f) f' (𝟙 T) e.hom
      ((Category.comp_id f').trans sq.flip.isoPullback_hom_fst.symm))
    (moduleUnboundedDerivedBaseChangeMap Λ f f' (𝟙 T ≫ g)
      (e.hom ≫ pullback.snd g f) ht)
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
    (moduleUnboundedDerivedInverseImageCompIso Λ g (𝟙 T))
    (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd g f) e.hom)
    (moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ)
    (eqToIso (congrArg (fun k : T ⟶ S => moduleUnboundedDerivedInverseImage Λ k)
      (Category.id_comp g)))
    (eqToIso (congrArg (fun k : X' ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
      sq.flip.isoPullback_hom_snd))
    (moduleUnboundedDerivedInverseImageIdIso Λ T)
    (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ g)
  · simp only [moduleUnboundedCartesianBaseChangeSourceIso, ← Iso.trans_assoc,
      eqToIso_trans, eqToIso_refl, Iso.refl_trans]
    rfl
  · exact moduleUnboundedDerivedBaseChangeMap_transport Λ f f' (𝟙 T ≫ g) g
      (e.hom ≫ pullback.snd g f) g' (Category.id_comp g)
      sq.flip.isoPullback_hom_snd ht sq.w.symm
  · exact moduleUnboundedDerivedBaseChangeMap_hComp Λ f (pullback.fst g f) f'
      g (𝟙 T) (pullback.snd g f) e.hom pullback.condition
      ((Category.comp_id f').trans sq.flip.isoPullback_hom_fst.symm) ht
end AlgebraicGeometry.Scheme.EtaleCohomology
