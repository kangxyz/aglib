/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Aglib.AlgebraicGeometry.Modules.Perfect.Local

/-!
# Compatibility names for native derived restriction and local perfectness

The predicates and perfect-restriction results have their sole implementation
in `PerfectComplexes.LocalRestriction`. Derived restriction is the native
functor in `Modules.DerivedCategory.Restriction`; these legacy names are
transparent delegates. They do not register duplicate global instances.
The original lower ordinary restriction and derived-isomorphism maps retain
exactly their existing native names.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] Scheme.Modules.standardHasDerivedCategory

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Legacy name for the same native exact derived restriction functor. -/
abbrev derivedRestrict : DerivedCategory X.Modules ⥤ DerivedCategory U.Modules :=
  Scheme.Modules.derivedRestrict j

/-- Legacy name for the canonical shift comparison, without a second instance. -/
abbrev derivedRestrictCommShift : (derivedRestrict j).CommShift ℤ :=
  Scheme.Modules.derivedRestrictCommShift j

/-- Legacy name for the canonical triangulated proof, without a second instance. -/
abbrev derivedRestrict_isTriangulated : (derivedRestrict j).IsTriangulated :=
  Scheme.Modules.derivedRestrict_isTriangulated j

/-- Legacy name for the same original native localization factorization. -/
abbrev derivedRestrictFactors :
    DerivedCategory.Q (C := X.Modules) ⋙ derivedRestrict j ≅
      restrict j ⋙ DerivedCategory.Q (C := U.Modules) :=
  Scheme.Modules.derivedRestrictFactors j

end AlgebraicGeometry.Scheme.Modules.Complex
