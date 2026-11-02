/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.IdentityExchangePasting
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBaseChangeExchange
public import
Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBCIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence

/-! # Original compactified exchange followed by a common-open refinement

Consecutive original exchange, identity-base unit contraction and the native
identity compositors identify the actual exchange with the raw exchange followed
by the original unit-induced refinement map. No proper Cartesian face is imposed
on the refinement, and no invertibility assumption replaces this equality.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wM wS wU' wM' wN wT

section Congruence
variable {U M S U' M' T : Scheme.{u}}
  (j : U ⟶ M) (p : M ⟶ S) (j' : U' ⟶ M') (p' : M' ⟶ T)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (a₀ a₁ : U' ⟶ U) (q : M' ⟶ M) (b₀ b₁ : T ⟶ S)
  (ea : a₀ = a₁) (eb : b₀ = b₁)
  (hj₀ : IsPullback a₀ j' j q) (hj₁ : IsPullback a₁ j' j q)
  (hp₀ : p' ≫ b₀ = q ≫ p) (hp₁ : p' ≫ b₁ = q ≫ p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wM'} (ModuleSheaf M' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Source and base equality transport preserve the exact original exchange. -/
theorem moduleUnboundedCompactifiedCommutingExchange_congr :
    moduleUnboundedCompactifiedCommutingExchange j p j' p' a₀ q b₀ hj₀ hp₀ Λ ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun a => moduleUnboundedDerivedInverseImage Λ a) ea)).hom
          (moduleUnboundedDerivedLowerShriek j' Λ ⋙ moduleUnboundedDerivedDirectImage Λ p') =
      Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ p)
          (eqToIso (congrArg (fun b => moduleUnboundedDerivedInverseImage Λ b) eb)).hom ≫
        moduleUnboundedCompactifiedCommutingExchange j p j' p' a₁ q b₁ hj₁ hp₁ Λ := by
  subst a₁
  subst b₁
  simp only [eqToIso_refl, Iso.refl_hom, Functor.whiskerRight_id',
    Functor.whiskerLeft_id', Category.comp_id, Category.id_comp]

end Congruence

variable {U M S U' M' N T : Scheme.{u}}
  (j : U ⟶ M) (p : M ⟶ S) (j' : U' ⟶ M') (p' : M' ⟶ T)
  (jN : U' ⟶ N) (h : N ⟶ M')
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion jN]
  (a : U' ⟶ U) (q : M' ⟶ M) (b : T ⟶ S)
  (hj : IsPullback a j' j q) (hp : p' ≫ b = q ≫ p)
  (sq : IsPullback jN (𝟙 U') h j')
  (ht : IsPullback a jN j (h ≫ q))
  (hpt : (h ≫ p') ≫ b = (h ≫ q) ≫ p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wM'} (ModuleSheaf M' Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf N Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- The original commuting exchange after a common-open refinement is the
original exchange followed by the original unit transition. -/
theorem moduleUnboundedCompactifiedCommutingExchange_refinement :
    moduleUnboundedCompactifiedCommutingExchange j p jN (h ≫ p') a (h ≫ q) b ht hpt Λ =
      moduleUnboundedCompactifiedCommutingExchange j p j' p' a q b hj hp Λ ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ a)
          (imageComparison (moduleUnboundedDerivedProperRefinementComparison jN j' h sq Λ)
            (moduleUnboundedDerivedDirectImageCompIso Λ p' h).symm) := by
  let htotal := sq.flip.paste_horiz hj
  have hproper : (h ≫ p') ≫ (𝟙 T ≫ b) = (h ≫ q) ≫ p := by
    simpa only [Category.id_comp] using hpt
  have hpasting := moduleUnboundedCompactifiedCommutingExchange_pasting
    j p j' p' jN (h ≫ p') a q b (𝟙 U') h (𝟙 T) hj hp sq.flip
    (Category.comp_id _) htotal hproper Λ
  have hi := moduleUnboundedCompactifiedIdentityBaseEquation jN j' h sq p' Λ
  have hc := identityExchangePasting
    (moduleUnboundedCompactifiedCommutingExchange j p j' p' a q b hj hp Λ)
    (moduleUnboundedCompactifiedCommutingExchange j' p' jN (h ≫ p') (𝟙 U') h (𝟙 T)
      sq.flip (Category.comp_id _) Λ)
    (moduleUnboundedCompactifiedCommutingExchange j p jN (h ≫ p')
      (𝟙 U' ≫ a) (h ≫ q) (𝟙 T ≫ b) htotal hproper Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ b (𝟙 T))
    (moduleUnboundedDerivedInverseImageCompIso Λ a (𝟙 U'))
    (moduleUnboundedDerivedInverseImageIdIso Λ T) (moduleUnboundedDerivedInverseImageIdIso Λ U')
    (imageComparison (moduleUnboundedDerivedProperRefinementComparison jN j' h sq Λ)
      (moduleUnboundedDerivedDirectImageCompIso Λ p' h).symm)
    (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k) (Category.id_comp b)))
    (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k) (Category.id_comp a)))
    (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ b)
    (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ a) hpasting hi
  have he := moduleUnboundedCompactifiedCommutingExchange_congr j p jN (h ≫ p')
    (𝟙 U' ≫ a) a (h ≫ q) (𝟙 T ≫ b) b (Category.id_comp a) (Category.id_comp b)
    htotal ht hproper hpt Λ
  exact (cancel_epi (Functor.whiskerLeft
    (moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedDirectImage Λ p)
    (eqToIso (congrArg (fun k => moduleUnboundedDerivedInverseImage Λ k)
      (Category.id_comp b))).hom)).mp (he.symm.trans hc)

end AlgebraicGeometry.Scheme.EtaleCohomology
