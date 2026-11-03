/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor

/-!
# Cohomology with the original field constants

The explicit structural-constants action and the original field-scheme action are
identified on the same underlying sheaf cohomology. No new cohomology realization is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original explicit-constants action is the original FScheme action.
Only the module-structure field is transported; the underlying Sheaf.H is unchanged. -/
def moduleCohomologyConstantsIso
    {k : Type u} [Field k] (X : FScheme k) (M : X.left.Modules) (q : ℕ) :
    (moduleCohomologyFunctorOfHom X.left (constants X) q).obj M ≅
      ModuleCat.of k (moduleCohomology k X M q) := by
  apply eqToIso
  exact congrArg
    (fun s : Module k (moduleCohomology k X M q) =>
      @ModuleCat.of k inferInstance (moduleCohomology k X M q) inferInstance s)
    (moduleCohomologyModuleOfHom_constants X M q)

/-- This is the identity on the same original underlying cohomology group. -/
theorem moduleCohomologyConstantsIso_hom_apply
    {k : Type u} [Field k] (X : FScheme k) (M : X.left.Modules) (q : ℕ)
    (x : (moduleCohomologyFunctorOfHom X.left (constants X) q).obj M) :
    (moduleCohomologyConstantsIso X M q).hom x = x := by
  rfl

end AlgebraicGeometry.Scheme.Cohomology
