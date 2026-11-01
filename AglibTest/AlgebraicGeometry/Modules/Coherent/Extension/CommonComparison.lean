/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.CommonComparison

/-! The comparison uses the same open and returns the two actual original maps. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

example {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (M N : X.Modules) (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    (e : M.restrict j ≅ N.restrict j) :
    ∃ (H : X.Modules) (a : H ⟶ M) (b : H ⟶ N),
      affineLocallyFiniteType X H ∧ Mono (biprod.lift a b) ∧
        IsIso ((restrictFunctor j).map a) ∧ IsIso ((restrictFunctor j).map b) :=
  Coherent.exists_coherent_common_comparison j M N hM hN e

end
