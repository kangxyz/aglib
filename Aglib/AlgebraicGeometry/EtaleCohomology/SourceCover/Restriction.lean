/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Pullback
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InjectiveRestriction
public import Aglib.CategoryTheory.Sites.RepresentedTransfer.ProductFamily

/-! # Actual source-chart restriction epis on genuine ringed injectives

Each original relative chart restriction is epic on every original etale
base test. This uses genuine ringed injectivity before scalar forgetting and
the original product-map mono; it does not require direct image to preserve
epimorphisms or the underlying abelian sheaf to be injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TorsionZMod.Ringed

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

/-- The original relative restriction, with no replacement source coefficient,
is epic on a genuine injective constant-ring module sheaf. -/
theorem sourceEtaleImageMap_epi_of_ringed_injective
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : X.Etale} (a : U ⟶ V) [Mono a]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I] :
    Epi ((Functor.whiskerRight (etaleProductSheafMap a) (directImage f)).app
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) := by
  let M := (SheafOfModules.toSheaf (constantRing X Λ)).obj I
  let r := (Functor.whiskerRight (etaleProductSheafMap a) (directImage f)).app M
  have hr : Epi r.hom := by
    let : ∀ T : S.Etaleᵒᵖ, Epi (r.hom.app T) := fun T => by
      let : Mono ((etaleProductMap a).app ((siteBaseChange f).obj T.unop)) :=
        CategoryTheory.MorphismProperty.Over.productMap_app_mono (@Etale) a _
      exact ModuleCat.Sheaf.ConstantRing.underlying_restriction_epi_of_injective.{
        u + 1, u, u + 1, 0}
        X.smallEtaleTopology Λ I ((etaleProductMap a).app ((siteBaseChange f).obj T.unop))
    exact NatTrans.epi_of_epi_app _
  exact (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).epi_of_epi_map hr

end AlgebraicGeometry.Scheme.EtaleCohomology
