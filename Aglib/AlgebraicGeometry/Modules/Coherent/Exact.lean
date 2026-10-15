/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Exact

/-!
# Exact coherent inclusion on locally Noetherian schemes

The guarded coherent category has the actual ambient sheaf short exact
sequences. The underlying objects and maps are those of the general
finite-type quasicoherent category.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The standard abelian exact structure on actual coherent sheaves. -/
def coherentExactStructure : ExactStructure (FiniteTypeSheaves X) := abelianExactStructure _

/-- Actual coherent inclusion is exact. -/
def coherentInclusion : ExactFunctor (coherentExactStructure X) (abelianExactStructure X.Modules)
  where
  toFunctor := finiteTypeSheavesToModules X
  map_conflation _ h := h.map_of_exact _

/-- Coherent exact sequences are precisely actual sheaf exact sequences. -/
theorem coherent_shortExact_iff (S : ShortComplex (FiniteTypeSheaves X)) :
    S.ShortExact ↔ (S.map (finiteTypeSheavesToModules X)).ShortExact := by
  constructor
  · exact fun h => h.map_of_exact _
  · intro h
    exact { exact := Functor.reflects_exact_of_faithful (finiteTypeSheavesToModules X) S h.exact
            mono_f := (finiteTypeSheavesToModules X).mono_of_mono_map h.mono_f
            epi_g := (finiteTypeSheavesToModules X).epi_of_epi_map h.epi_g }

end AlgebraicGeometry.Scheme.Modules.Coherent
