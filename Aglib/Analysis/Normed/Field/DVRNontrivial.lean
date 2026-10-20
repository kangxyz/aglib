/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.Normed.Field.DVR
public import Aglib.Analysis.Normed.Field.Nontrivial

/-!
# Nontriviality of a compatible DVR norm

Source: `R5Lab.Aglib.Analysis.Normed.Field.DVRNontrivial`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open IsLocalRing
namespace NormedField.NormCompatible
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A compatible norm on a genuine DVR fraction field is necessarily nontrivial. -/
@[instance_reducible]
def nontrivialNormOfDVR {F : Type u} [NormedField F]
    [Algebra R F] [IsFractionRing R F] (H : NormCompatible R F) : NontriviallyNormedField F := by
  let π := Classical.choose (IsDiscreteValuationRing.exists_irreducible R)
  have hπ := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible R)
  exact NormedField.nontrivialOfSmallUnit
    (Units.mk0 (algebraMap R F π) ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      hπ.ne_zero))
    (H.norm_map_irreducible_lt_one hπ)

end NormedField.NormCompatible
