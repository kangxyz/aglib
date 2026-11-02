/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationBaseModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoExchange

/-! # Original source-only exchange between independent base derived models -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

private theorem source_exchange_of_base_transport
    {A A' B E₀ E₁ : Type*}
    [Category* A] [Category* A'] [Category* B] [Category* E₀] [Category* E₁]
    {J : A ⥤ B} {J' : A' ⥤ B} {V : A ⥤ A'}
    {R₀ : B ⥤ E₀} {R₁ : B ⥤ E₁} {G E : E₀ ⥤ E₁} {I : B ⥤ B}
    (β : R₀ ⋙ G ⟶ I ⋙ R₁) (d : I ≅ 𝟭 B)
    (ν : G ≅ E) (τ : R₀ ⋙ E ≅ R₁) (α : J ⋙ I ≅ V ⋙ J')
    (hβ : ∀ K, β.app K ≫ R₁.map (d.hom.app K) =
      ν.hom.app (R₀.obj K) ≫ τ.hom.app K) :
    compositeExchange β α =
      (Functor.isoWhiskerLeft (J ⋙ R₀) ν ≪≫ Functor.associator J R₀ E ≪≫
        Functor.isoWhiskerLeft J τ ≪≫
        Functor.isoWhiskerRight ((Functor.rightUnitor J).symm ≪≫
          Functor.isoWhiskerLeft J d.symm ≪≫ α) R₁ ≪≫
        Functor.associator V J' R₁).hom := by
  ext K
  have hb := congrArg (fun z => z ≫ R₁.map (d.inv.app (J.obj K))) (hβ (J.obj K))
  simp only [Category.assoc, ← R₁.map_comp, Iso.hom_inv_id_app, R₁.map_id,
    Functor.comp_obj, Functor.id_obj, Category.comp_id] at hb
  simp only [compositeExchange_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id, R₁.map_comp, Functor.comp_obj, Functor.id_obj]
  rw [hb]
  simp only [Category.assoc]

universe u wX wX' wM wS₀ wS₁
variable {X X' M S : Scheme.{u}} (e : X' ≅ X) (j : X ⟶ M) [IsOpenImmersion j]
  (p : M ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ))
  (hM : HasDerivedCategory.{wM} (ModuleSheaf M Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))

local notation "J" => @moduleUnboundedDerivedLowerShriek X M j _ Λ _ hX hM
local notation "R₀" => @moduleUnboundedDerivedDirectImage Λ _ S M p hS₀ hM
local notation "R₁" => @moduleUnboundedDerivedDirectImage Λ _ S M p hS₁ hM
local notation "V" => @moduleUnboundedDerivedInverseImage Λ _ X X' e.hom hX hX'
local notation "J'" => @moduleUnboundedDerivedLowerShriek X' M (e.hom ≫ j) _ Λ _ hX' hM

/-- This is literally the original compactified map with explicit independent base models. -/
abbrev moduleUnboundedBaseModelSourceExchange :=
  @moduleUnboundedCompactifiedBaseChangeMap X M S X' M S
    j p (e.hom ≫ j) p e.hom (𝟙 M) (𝟙 S) _ _
    (isPullback_sourceIsoOpen e j) (isPullback_sourceIsoProperIdentity p) Λ _
    hX hM hS₀ hX' hM hS₁

/-- The actual exchange is the original localization/base-model normalizer
followed by the original source isomorphism; no base models are identified. -/
theorem moduleUnboundedBaseModelSourceExchange_eq :
    moduleUnboundedBaseModelSourceExchange e j p Λ hX hX' hM hS₀ hS₁ =
      (Functor.isoWhiskerLeft (J ⋙ R₀)
          (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁) ≪≫
        Functor.associator J R₀
          (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor ≪≫
        Functor.isoWhiskerLeft J
          (moduleUnboundedDerivedDirectImageChangeBaseModel Λ hS₀ hS₁ p hM) ≪≫
        @moduleUnboundedCompactifiedSourceIso X X' M S e j _ p Λ _ hX hX' hM hS₁).hom := by
  exact source_exchange_of_base_transport
    (@moduleUnboundedDerivedBaseChangeMap Λ _ M S M S
      hM hS₀ hM hS₁ p p (𝟙 S) (𝟙 M)
      (isPullback_sourceIsoProperIdentity p).w.symm)
    (@moduleUnboundedDerivedInverseImageIdIso Λ _ M hM)
    (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁)
    (moduleUnboundedDerivedDirectImageChangeBaseModel Λ hS₀ hS₁ p hM)
    (@moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso X' X M M
      e.hom (e.hom ≫ j) j (𝟙 M) _ _
      (isPullback_sourceIsoOpen e j) Λ _ hX' hX hM hM)
    (moduleUnboundedDerivedBaseChangeMap_identity_baseModel Λ hS₀ hS₁ p hM
      (isPullback_sourceIsoProperIdentity p).w.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
