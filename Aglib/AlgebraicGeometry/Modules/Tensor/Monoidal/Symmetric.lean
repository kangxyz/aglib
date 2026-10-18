/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic

/-!
# The symmetric monoidal category of scheme modules

The existing braiding `tensorSheafBraiding` (the sheafified presheaf braiding) makes the monoidal
category of scheme modules of `Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic` symmetric,
with no hypothesis on the scheme. The hexagons and the symmetry are obtained through
`BraidedCategory.ofFaithful` and `SymmetricCategory.ofFaithful` along the identity functor into
Mathlib's localized symmetric monoidal category of module presheaves.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory BraidedCategory Localization.Monoidal

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The braiding condition along `toLocalizedMonoidal`: the existing braiding is carried to the
localized braiding. -/
theorem toLocalizedMonoidal_μ_comp_map_braiding (M N : X.Modules) :
    Functor.LaxMonoidal.μ (toLocalizedMonoidal X) M N ≫
        (toLocalizedMonoidal X).map (tensorSheafBraiding X M N).hom =
      (β_ ((toLocalizedMonoidal X).obj M) ((toLocalizedMonoidal X).obj N)).hom ≫
        Functor.LaxMonoidal.μ (toLocalizedMonoidal X) N M :=
  μOf_hom_comp_map_braiding (toLocalizedMonoidalCounitIso X M) (toLocalizedMonoidalCounitIso X N)

/-- Scheme modules form a braided monoidal category under the existing braiding. -/
instance braidedCategory : BraidedCategory X.Modules :=
  BraidedCategory.ofFaithful (toLocalizedMonoidal X) (fun M N ↦ tensorSheafBraiding X M N)
    (toLocalizedMonoidal_μ_comp_map_braiding X)

/-- The identity into the localized monoidal category is a braided functor. -/
instance instBraidedToLocalizedMonoidal : (toLocalizedMonoidal X).Braided where
  braided := toLocalizedMonoidal_μ_comp_map_braiding X

/-- Scheme modules form a symmetric monoidal category under the existing tensor maps and
braiding. -/
instance symmetricCategory : SymmetricCategory X.Modules :=
  SymmetricCategory.ofFaithful (toLocalizedMonoidal X)

theorem braiding_eq_tensorSheafBraiding (M N : X.Modules) :
    β_ M N = tensorSheafBraiding X M N :=
  rfl

end AlgebraicGeometry.Scheme.Modules
