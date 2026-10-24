/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Connecting
public import Aglib.RingTheory.Finiteness.Exact

/-!
# Adjacent-degree finite generation for original module-sheaf cohomology

For an actual short exact sequence `0 → A → B → C → 0`, the original
linear connecting map gives two finite-generation implications over a
Noetherian coefficient ring. Finite `Hⁿ(B)` and `Hⁿ⁺¹(A)` imply finite
`Hⁿ(C)`; finite `Hⁿ(C)` and `Hⁿ⁺¹(B)` imply finite `Hⁿ⁺¹(A)`.
No finiteness of the underlying abelian groups is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify

/-- Finite cohomology of the middle term and finite next-degree cohomology
of the first term imply finite cohomology of the last term. -/
theorem finite_cohomology_X₃_of_shortExact [IsNoetherianRing R]
    (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R ((cohomology J R q).obj S.X₂)]
    [Module.Finite R ((cohomology J R (q + 1)).obj S.X₁)] :
    Module.Finite R ((cohomology J R q).obj S.X₃) :=
  Module.Finite.of_exact_of_isNoetherian _ _
    (cohomologyδ_exact_left J R S hS q (q + 1) rfl)

/-- Finite cohomology of the last term and finite next-degree cohomology
of the middle term imply finite next-degree cohomology of the first term. -/
theorem finite_cohomology_X₁_of_shortExact [IsNoetherianRing R]
    (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R ((cohomology J R q).obj S.X₃)]
    [Module.Finite R ((cohomology J R (q + 1)).obj S.X₂)] :
    Module.Finite R ((cohomology J R (q + 1)).obj S.X₁) :=
  Module.Finite.of_exact_of_isNoetherian _ _
    (cohomologyδ_exact_right J R S hS q (q + 1) rfl)

end ModuleCat.Sheaf
