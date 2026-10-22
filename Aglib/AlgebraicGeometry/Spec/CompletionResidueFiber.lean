/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.RingTheory.AdicCompletion.LocalResidue
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The literal closed fibre after local completion

The residue-field isomorphism induced by the actual completion map identifies
the completed scheme's literal residue fibre with the original residue fibre.
The comparison retains its equation with the two original inclusions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.LocalRing

universe u

section PullbackComparison

variable {S T K L X : Scheme.{u}}
  (f : X ⟶ S) (c : T ⟶ S) (r : K ⟶ S) (t : L ⟶ T)
  (e : L ≅ K) (h : t ≫ c = e.hom ≫ r)

/-- Canonical residue-fibre comparison for a base-change square whose map on
the residue bases is an isomorphism. -/
def residueFiberBaseChangeIso : pullback (pullback.snd f c) t ≅ pullback f r :=
  pullbackLeftPullbackSndIso f c t ≪≫
    pullback.congrHom rfl h ≪≫
      (pullbackLeftPullbackSndIso f r e.hom).symm ≪≫
        asIso (pullback.fst (pullback.snd f r) e.hom)

/-- The comparison is over the original scheme, not merely an abstract
isomorphism between the two fibres. -/
@[reassoc (attr := simp)]
theorem residueFiberBaseChangeIso_hom_fst :
    (residueFiberBaseChangeIso f c r t e h).hom ≫ pullback.fst f r =
      pullback.fst (pullback.snd f c) t ≫ pullback.fst f c := by
  simp [residueFiberBaseChangeIso, pullback.map, pullback.lift_fst, Category.assoc]

end PullbackComparison

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The spectrum map of the original maximal-ideal completion algebra map. -/
abbrev completionSpecMap :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ⟶ Spec (.of R) :=
  Spec.algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- The spectrum isomorphism comes from the actual induced residue-field map. -/
def completionResidueSpecIso :
    Spec (.of (IsLocalRing.ResidueField
      (AdicCompletion (IsLocalRing.maximalIdeal R) R))) ≅
        Spec (.of (IsLocalRing.ResidueField R)) :=
  Scheme.Spec.mapIso (RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    (AdicCompletion.residueField_map_bijective R)).toCommRingCatIso.op

/-- The original completion map commutes with the two original residue maps. -/
@[reassoc]
theorem completionResidueSpecIso_square :
    residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R) ≫ completionSpecMap R =
      (completionResidueSpecIso R).hom ≫ residueSpecMap R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

variable {R} {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The literal closed fibre of the actual completion base change is
canonically isomorphic to the original literal closed fibre. -/
def completionResidueFiberIso :
    pullback (pullback.snd f (completionSpecMap R))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ≅
        pullback f (residueSpecMap R) :=
  residueFiberBaseChangeIso f (completionSpecMap R) (residueSpecMap R)
    (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (completionResidueSpecIso R) (completionResidueSpecIso_square R)

/-- The completed-fibre comparison preserves the specified original
inclusions into the original proper scheme. -/
@[reassoc (attr := simp)]
theorem completionResidueFiberIso_hom_fst :
    (completionResidueFiberIso f).hom ≫ pullback.fst f (residueSpecMap R) =
      pullback.fst (pullback.snd f (completionSpecMap R))
        (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ≫
          pullback.fst f (completionSpecMap R) :=
  residueFiberBaseChangeIso_hom_fst _ _ _ _ _ _

end AlgebraicGeometry.Scheme.LocalRing
