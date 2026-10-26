/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Basic

/-! # Symmetry of the chosen ringed-site tensor

The original sheafified presheaf braiding is carried by the faithful identity
to the localized braiding. This proves the hexagons and symmetry for the same
chosen tensor data, conditional on their explicit monoidal localization input.
-/

@[expose] public section

noncomputable section

universe uC vC uR

open CategoryTheory MonoidalCategory BraidedCategory Localization.Monoidal

namespace SheafOfModulesOfCommRing

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR}) [HasSheafify J AddCommGrpCat.{uR}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{uR}]
  [(presheafLocalIso R).IsMonoidal]

/-- The braiding condition along `toLocalizedMonoidal`: the existing braiding is carried to the
localized braiding. -/
theorem toLocalizedMonoidal_μ_comp_map_braiding (M N : SheafOfModulesOfCommRing R) :
    Functor.LaxMonoidal.μ (toLocalizedMonoidal R) M N ≫
        (toLocalizedMonoidal R).map (tensorBraiding R M N).hom =
      (β_ ((toLocalizedMonoidal R).obj M) ((toLocalizedMonoidal R).obj N)).hom ≫
        Functor.LaxMonoidal.μ (toLocalizedMonoidal R) N M :=
  μOf_hom_comp_map_braiding (toLocalizedMonoidalCounitIso R M) (toLocalizedMonoidalCounitIso R N)

/-- Ringed-site module sheaves form a braided monoidal category under the existing braiding. -/
instance braidedCategory : BraidedCategory (SheafOfModulesOfCommRing R) :=
  BraidedCategory.ofFaithful (toLocalizedMonoidal R) (fun M N ↦ tensorBraiding R M N)
    (toLocalizedMonoidal_μ_comp_map_braiding R)

/-- The identity into the localized monoidal category is a braided functor. -/
instance instBraidedToLocalizedMonoidal : (toLocalizedMonoidal R).Braided where
  braided := toLocalizedMonoidal_μ_comp_map_braiding R

/-- Ringed-site module sheaves form a symmetric monoidal category under the existing tensor maps and
braiding. -/
instance symmetricCategory : SymmetricCategory (SheafOfModulesOfCommRing R) :=
  SymmetricCategory.ofFaithful (toLocalizedMonoidal R)

theorem braiding_eq_tensorBraiding (M N : SheafOfModulesOfCommRing R) :
    β_ M N = tensorBraiding R M N :=
  rfl

end SheafOfModulesOfCommRing
