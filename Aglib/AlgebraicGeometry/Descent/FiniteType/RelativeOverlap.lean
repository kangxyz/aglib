/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# An overlap as an actual restriction of a relative diagonal

For two opens of a scheme over a fixed base, the overlap maps into their
relative product. The resulting square over the relative diagonal is
cartesian, with an explicit comparison to the canonical pullback. This
is the map-level supplier for varying-source separatedness descent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeOverlap

variable {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)

/-- The product of the two specified opens over the fixed base. -/
abbrev product : Scheme.{u} := pullback (U.ι ≫ f) (V.ι ≫ f)

/-- The literal map of the product chart into the diagonal target. -/
def productToDiagonalTarget : product f U V ⟶ pullback f f :=
  pullback.map (U.ι ≫ f) (V.ι ≫ f) f f U.ι V.ι (𝟙 S) (by simp) (by simp)

instance productToDiagonalTarget_isOpenImmersion :
    IsOpenImmersion (productToDiagonalTarget f U V) := by
  dsimp [productToDiagonalTarget]
  infer_instance

/-- The actual overlap arrow into the relative product of its two charts. -/
def toProduct : (U ⊓ V).toScheme ⟶ product f U V :=
  pullback.lift (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (by
    simp only [← Category.assoc, Scheme.homOfLE_ι])

@[reassoc (attr := simp)]
lemma toProduct_fst : toProduct f U V ≫ pullback.fst (U.ι ≫ f) (V.ι ≫ f) =
    X.homOfLE inf_le_left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toProduct_snd : toProduct f U V ≫ pullback.snd (U.ι ≫ f) (V.ι ≫ f) =
    X.homOfLE inf_le_right :=
  pullback.lift_snd _ _ _

/-- The overlap square is the actual base change of the relative diagonal. -/
lemma isPullback_toProduct :
    IsPullback (U ⊓ V).ι (toProduct f U V)
      (pullback.diagonal f) (productToDiagonalTarget f U V) := by
  let H := isPullback_opens_inf U V
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (H.isoPullback ≪≫ (pullbackDiagonalMapIdIso U.ι V.ι f).symm) ?_ ?_
  · apply pullback.hom_ext <;>
      simp [productToDiagonalTarget, toProduct, Scheme.homOfLE_ι]
  · simp [productToDiagonalTarget, Iso.trans_hom, H.isoPullback_hom_fst_assoc]
  · apply pullback.hom_ext <;>
      simp [productToDiagonalTarget, Iso.trans_hom, toProduct,
        H.isoPullback_hom_fst, H.isoPullback_hom_snd]

/-- The overlap arrow is locally of finite type without any finiteness
assumption on the structural morphism to the fixed base. -/
lemma locallyOfFiniteType_toProduct : LocallyOfFiniteType (toProduct f U V) := by
  have : LocallyOfFiniteType
      (toProduct f U V ≫ pullback.fst (U.ι ≫ f) (V.ι ≫ f)) := by
    rw [toProduct_fst]
    infer_instance
  exact locallyOfFiniteType_of_comp (toProduct f U V) (pullback.fst (U.ι ≫ f) (V.ι ≫ f))

/-- A separated structural morphism has closed overlap arrows. -/
lemma isClosedImmersion_toProduct [IsSeparated f] :
    IsClosedImmersion (toProduct f U V) :=
  @MorphismProperty.IsStableUnderBaseChange.of_isPullback
    Scheme.{u} _ (@IsClosedImmersion) IsClosedImmersion.isStableUnderBaseChange
    (product f U V) X (U ⊓ V).toScheme (pullback f f)
    (productToDiagonalTarget f U V) (pullback.diagonal f)
    (U ⊓ V).ι (toProduct f U V) (isPullback_toProduct f U V) inferInstance

end AlgebraicGeometry.Scheme.RelativeOverlap
