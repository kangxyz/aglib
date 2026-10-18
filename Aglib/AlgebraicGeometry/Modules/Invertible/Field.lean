/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Actual line bundles and singleton bases over a field

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/Picard/Field.lean`, SHA-256
  `afe9026e554a65d135ca3f12950ea8ce2b9d32b17a2ec7c23ddbec5fd8ebe50f`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open Module
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

theorem fieldLineBundle_trivial (K : Type u) [Field K] (L : LineBundle (Spec (.of K))) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec (.of K)).ringCatSheaf) := by
  let x : Spec (.of K) := IsLocalRing.closedPoint K
  obtain ⟨U, hx, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
  have hU : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    exact (Subsingleton.elim x y) ▸ hx
  have : IsIso U.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι (by simpa using hU)
  let j := inv U.ι
  let e' := ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.val).symm ≪≫ e
  exact ⟨((Scheme.Modules.pullbackId _).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id U.ι)).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackComp j U.ι).app L.val).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e' ≪≫ pullbackUnitIso j⟩

/-- A line bundle associated to a module over a field supplies an actual
singleton basis of that module. -/
def basisOfTildeRankOne (K : Type u) [Field K] (M : ModuleCat.{u} K)
    (h : IsLocallyRankOne (Spec (.of K)) (tilde M)) :
    Basis PUnit.{u + 1} K M := by
  let e := (fieldLineBundle_trivial K ⟨tilde M, h⟩).some
  let e' : M ≅ ModuleCat.of K K := (tilde.isoTop (R := CommRingCat.of K) M) ≪≫
    (moduleSpecΓFunctor (R := .of K)).mapIso e ≪≫
      (tilde.isoTop (R := CommRingCat.of K) (ModuleCat.of K K)).symm
  exact (Basis.singleton PUnit K).map e'.toLinearEquiv.symm

end AlgebraicGeometry.Scheme.Modules.Invertible
end
