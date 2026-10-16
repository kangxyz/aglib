/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers

/-!
# Coherent homology of the original native single

The original homology of a native single is its coefficient in the
specified degree and zero in every other degree. The comparison is the
sole native single/homology isomorphism, with the supplied derived
category retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- The native single of a coherent module has coherent original homology. -/
theorem coherentHomologyObjects_single (M : X.Modules)
    (hM : QuasiCoherent.affineLocallyFiniteType X M) (n : ℤ) :
    coherentHomologyObjects X ((DerivedCategory.Plus.singleFunctor X.Modules n).obj M) := by
  intro i
  by_cases hi : i = n
  · subst i
    exact (QuasiCoherent.affineLocallyFiniteType X).prop_of_iso
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).app M).symm hM
  · apply (QuasiCoherent.affineLocallyFiniteType X).prop_of_isZero
    by_cases hlt : i < n
    · exact DerivedCategory.Plus.isZero_homology_of_isGE _ n i hlt
    · exact DerivedCategory.Plus.isZero_homology_of_isLE _ n i (by omega)

/-- The coherent-homology property of the original native single is precisely
coherence of its original coefficient. -/
theorem coherentHomologyObjects_single_iff (M : X.Modules) (n : ℤ) :
    coherentHomologyObjects X ((DerivedCategory.Plus.singleFunctor X.Modules n).obj M) ↔
      QuasiCoherent.affineLocallyFiniteType X M := by
  refine ⟨fun h => ?_, fun h => coherentHomologyObjects_single X M h n⟩
  exact (QuasiCoherent.affineLocallyFiniteType X).prop_of_iso
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).app M) (h n)

end AlgebraicGeometry.Scheme.Modules
