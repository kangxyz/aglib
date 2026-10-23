/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AmitsurSections
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Exactness of the actual spectrum-section Amitsur complex

This is a statement about the original algebraic conerve and its spectrum
sections, not yet a geometric basis-acyclicity statement for arbitrary families.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (R : Type u) [CommRing R]

instance : PreservesFiniteLimits (moduleAdditiveLift R) :=
  inferInstanceAs (PreservesFiniteLimits
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}))

instance : PreservesFiniteColimits (moduleAdditiveLift R) := by
  let : PreservesColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u, u, 0, 0} R
  let : PreservesColimitsOfSize.{0, 0} (moduleAdditiveLift R) :=
    inferInstanceAs (PreservesColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}))
  exact PreservesColimitsOfSize0.preservesFiniteColimits (moduleAdditiveLift R)

variable (F : (Spec (CommRingCat.of R)).Modules) [F.IsQuasicoherent]
  (S : Type u) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

/-- Faithfully flat descent makes the original spectrum-section complex exact
in positive degree, for arbitrary quasi-coherent coefficients. -/
theorem amitsurSectionsComplex_exactAt_succ (n : ℕ) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj (amitsurSections R F S)).ExactAt
      (n + 1) := by
  apply HomologicalComplex.ExactAt.of_iso _ (amitsurSectionsComplexIso R F S)
  rw [HomologicalComplex.exactAt_iff]
  exact ((HomologicalComplex.exactAt_iff _ _).mp
    (ModuleCat.Amitsur.complex_exactAt_succ R S (moduleSpecΓFunctor.obj F) n)).map
      (moduleAdditiveLift R)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
