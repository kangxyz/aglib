/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Native exact derived restriction of scheme module sheaves

Relocated from `Modules/Perfect/LocalRestriction.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`, SHA-256
`427c224a2e1080a356308dc5dfa3cd61cbbaa339d138d0a1a058f2e3c7f2adbc`.
The exact native functor, factorization and components are unchanged.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Scheme.Modules.standardHasDerivedCategory

variable {V U X : Scheme.{u}}

variable (j : U ⟶ X) [IsOpenImmersion j]

/-- The native derived functor of exact geometric restriction. -/
def derivedRestrict : DerivedCategory X.Modules ⥤ DerivedCategory U.Modules :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategory

instance derivedRestrictCommShift : (derivedRestrict j).CommShift ℤ :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.CommShift ℤ)

instance derivedRestrict_isTriangulated : (derivedRestrict j).IsTriangulated :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.IsTriangulated)

/-- The actual native localization factorization for geometric restriction. -/
def derivedRestrictFactors :
    DerivedCategory.Q (C := X.Modules) ⋙ derivedRestrict j ≅
      Complex.restrict j ⋙ DerivedCategory.Q (C := U.Modules) :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors

namespace Complex

/-- Restrict an actual isomorphism in the quasi-isomorphism localization. -/
def restrictDerivedIso {K L : CochainComplex X.Modules ℤ}
    (e : (DerivedCategory.Q (C := X.Modules)).obj K ≅ (DerivedCategory.Q (C := X.Modules)).obj L) :
    (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ≅ (DerivedCategory.Q (C :=
      U.Modules)).obj ((restrict j).obj L) :=
  ((derivedRestrictFactors j).app K).symm ≪≫
    (derivedRestrict j).mapIso e ≪≫ (derivedRestrictFactors j).app L

end Complex
end AlgebraicGeometry.Scheme.Modules
