/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImageIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitSource

/-! # Original contraction of an independently modelled identity value -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

private theorem identityImageContraction
    {A : Type*} [Category* A] (R : A ⥤ A) (e : R ≅ 𝟭 A)
    {U K : A} (a : U ⟶ R.obj K) :
    a ≫ R.map (e.inv.app K) ≫
        (e.hom.app (R.obj K) ≫ 𝟙 (R.obj K)) ≫ e.hom.app K =
      a ≫ 𝟙 (R.obj K) ≫ e.hom.app K := by
  have hi : e.hom.app (R.obj K) ≫ 𝟙 (R.obj K) = e.hom.app (R.obj K) :=
    Category.comp_id _
  have hn := e.hom.naturality (e.inv.app K)
  change R.map (e.inv.app K) ≫ e.hom.app (R.obj K) =
    e.hom.app K ≫ e.inv.app K at hn
  have hc := hn.trans (e.hom_inv_id_app K)
  rw [hi]
  have ht := congrArg (fun t => a ≫ t ≫ e.hom.app K) hc
  simpa only [Category.assoc] using ht

universe u wX wM
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hM : HasDerivedCategory.{wM} (ModuleSheaf X Λ)]

/-- The original identity value is contracted without identifying its two models. -/
def moduleUnboundedSingleIdentityValueIso :
    @moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hM ⋙
      @moduleUnboundedDerivedDirectImage Λ _ X X (𝟙 X) hX hM ≅
      𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX) := by
  letI := hX
  have hi := @moduleUnboundedLowerShriekToDirectImage_isIso_of_isIso Λ _ X X (𝟙 X) _ hX hM
  exact Functor.isoWhiskerRight
      (@asIso _ _ _ _ (@moduleUnboundedLowerShriekToDirectImage Λ _ X X (𝟙 X) _ hX hM) hi)
      (@moduleUnboundedDerivedDirectImage Λ _ X X (𝟙 X) hX hM) ≪≫
    @moduleUnboundedDerivedDirectImageOverIso Λ _ X X X hX hX hM
      (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp (𝟙 X)) ≪≫
    @moduleUnboundedDerivedDirectImageIdIso Λ _ X hX

omit hM in
/-- With the endpoint model, contraction is precisely the two original identity maps. -/
theorem moduleUnboundedSingleIdentityValueIso_sameModel :
    moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ =
      Functor.isoWhiskerRight (@moduleUnboundedDerivedLowerShriekIdIso Λ _ X hX)
        (@moduleUnboundedDerivedDirectImage Λ _ X X (𝟙 X) hX hX) ≪≫
      Functor.leftUnitor (@moduleUnboundedDerivedDirectImage Λ _ X X (𝟙 X) hX hX) ≪≫
        @moduleUnboundedDerivedDirectImageIdIso Λ _ X hX := by
  let := hX
  apply Iso.ext
  simp only [moduleUnboundedSingleIdentityValueIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, asIso_hom,
    moduleUnboundedLowerShriekToDirectImage_id,
    moduleUnboundedDerivedDirectImageOverIso_identityTarget,
    Functor.isoWhiskerLeft_hom]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  simpa only [Category.assoc] using
    identityImageContraction (K := K) (moduleUnboundedDerivedDirectImage Λ (𝟙 X))
    (moduleUnboundedDerivedDirectImageIdIso Λ X)
    ((moduleUnboundedDerivedDirectImage Λ (𝟙 X)).map
      ((moduleUnboundedDerivedLowerShriekIdIso Λ X).hom.app K))

end AlgebraicGeometry.Scheme.EtaleCohomology
