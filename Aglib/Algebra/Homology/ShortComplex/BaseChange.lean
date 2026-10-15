/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Exactness
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Cycle exactness from the original scalar-extension homology map

Surjectivity of the native scalar-extension map on homology makes the
original cycle sequence exact after tensoring with the target algebra.
The proof uses the native adjunction mate and the original algebra tensor
product, retaining its differential maps. No flatness or finiteness is
assumed in this exactness statement.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe u v w

variable {R : Type u} {B : Type w} [CommRing R] [CommRing B] [Algebra R B]
    (S : ShortComplex (ModuleCat.{max v w} R))

/-- Surjectivity of the original homology base-change mate implies tensor exactness of
the original cycle inclusion and outgoing differential, with no flatness assumption. -/
theorem lTensor_cycles_exact_of_epi_homologyBaseChangeMap
    [Epi (ModuleCat.homologyBaseChangeMap (algebraMap R B) S)] :
    Function.Exact (S.iCycles.hom.lTensor B) (S.g.hom.lTensor B) := by
  let F : ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} B :=
    ModuleCat.extendScalars (algebraMap R B)
  let adj := ModuleCat.extendRestrictScalarsAdj.{v, u, w} (algebraMap R B)
  let : Epi (adj.homologyComparison S) := inferInstance
  have h := adj.exact_map_cyclesShortComplex_of_epi_homologyComparison S
  have hz : S.g.hom.comp S.iCycles.hom = 0 :=
    congrArg ModuleCat.Hom.hom S.iCycles_g
  let T : ShortComplex (ModuleCat.{max v w} B) := moduleCatMk
    (S.iCycles.hom.baseChange B) (S.g.hom.baseChange B) (by
      rw [← LinearMap.baseChange_comp, hz, LinearMap.baseChange_zero])
  let e : S.cyclesShortComplex.map F ≅ T := ShortComplex.isoMk
    (ModuleCat.extendScalarsAlgebraObjIso R B S.cycles)
    (ModuleCat.extendScalarsAlgebraObjIso R B S.X₂)
    (ModuleCat.extendScalarsAlgebraObjIso R B S.X₃)
    (ModuleCat.extendScalarsAlgebraObjIso_naturality R B S.iCycles).symm
    (ModuleCat.extendScalarsAlgebraObjIso_naturality R B S.g).symm
  have hT := (ShortExact.moduleCat_exact_iff_function_exact T).mp (exact_of_iso e h)
  exact hT

end CategoryTheory.ShortComplex
