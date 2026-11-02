/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Symmetric

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
  SheafOfModulesOfCommRing.toLocalizedMonoidal_μ_comp_map_braiding X.sheaf M N

/-- Scheme modules form a braided monoidal category under the existing braiding. -/
instance braidedCategory : BraidedCategory X.Modules :=
  SheafOfModulesOfCommRing.braidedCategory X.sheaf

/-- The identity into the localized monoidal category is a braided functor. -/
instance instBraidedToLocalizedMonoidal : (toLocalizedMonoidal X).Braided :=
  SheafOfModulesOfCommRing.instBraidedToLocalizedMonoidal X.sheaf

/-- Scheme modules form a symmetric monoidal category under the existing tensor maps and
braiding. -/
instance symmetricCategory : SymmetricCategory X.Modules :=
  SheafOfModulesOfCommRing.symmetricCategory X.sheaf

/-- The original Scheme symmetry is the actual generic chosen symmetry. -/
theorem symmetricCategory_eq_generic :
    symmetricCategory X = SheafOfModulesOfCommRing.symmetricCategory X.sheaf := rfl

theorem braiding_eq_tensorSheafBraiding (M N : X.Modules) :
    β_ M N = tensorSheafBraiding X M N :=
  rfl

end AlgebraicGeometry.Scheme.Modules
