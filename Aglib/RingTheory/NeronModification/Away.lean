/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Basic

/-! # Néron modifications away from the distinguished element

The original base map becomes an isomorphism after inverting the distinguished element.
No regularity or finiteness assumption on the original ring or relation family is required.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Algebra.NeronModification

variable {B : Type*} [CommRing B] {ι : Type*}

/-- The original map is the canonical algebra map of the two quotient algebras. -/
theorem of_eq_algebraMap (p : B) (g : ι → B) :
    of p g = algebraMap B (Modification p g) := rfl

/-- Map the modification to the original localization using the actual fractions `gᵢ / p`. -/
def toAway (p : B) (g : ι → B) :
    Modification p g →+* Localization.Away p :=
  lift p g (algebraMap B (Localization.Away p))
    (fun i => IsLocalization.Away.invSelf p * algebraMap B (Localization.Away p) (g i))
    (fun i => by rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul])
    (IsLocalization.Away.algebraMap_isUnit p).isRegular

private theorem toAway_of (p : B) (g : ι → B) (b : B) :
    toAway p g (of p g b) = algebraMap B (Localization.Away p) b :=
  lift_of p g _ _ _ _ b

/-- The localized original coefficient map from the base to its modification. -/
def awayForward (p : B) (g : ι → B) :
    Localization.Away p →+* Localization.Away (M := Modification p g) (of p g p) :=
  IsLocalization.Away.map (R := B) (P := Modification p g) (Localization.Away p)
    (Localization.Away (M := Modification p g) (of p g p)) (of p g) p

private theorem awayForward_base (p : B) (g : ι → B) (b : B) :
    awayForward p g (algebraMap B (Localization.Away p) b) =
      (@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance) (of p g b) :=
  by simp only [awayForward, IsLocalization.Away.map, IsLocalization.map_eq]

/-- Extend the actual fractional point to the localization of the modification. -/
def awayBackward (p : B) (g : ι → B) :
    Localization.Away (M := Modification p g) (of p g p) →+* Localization.Away p :=
  IsLocalization.Away.lift (of p g p)
    (g := toAway p g) (by
      rw [toAway_of]
      exact IsLocalization.Away.algebraMap_isUnit p)

private theorem awayBackward_base (p : B) (g : ι → B) (x : Modification p g) :
    awayBackward p g
        ((@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance) x) =
      toAway p g x :=
  IsLocalization.Away.lift_eq _ _ _

/-- The fractional inverse is a left inverse to the localized coefficient map. -/
theorem awayBackward_comp_forward (p : B) (g : ι → B) :
    (awayBackward p g).comp (awayForward p g) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers p)
  apply RingHom.ext
  intro b
  change awayBackward p g (awayForward p g (algebraMap B (Localization.Away p) b)) = _
  rw [awayForward_base, awayBackward_base, toAway_of]
  rfl

/-- The map to the original localization factors the actual localization of the modification. -/
theorem awayForward_comp_toAway (p : B) (g : ι → B) :
    (awayForward p g).comp (toAway p g) =
      (@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance) := by
  let f := (@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance)
  let b := f.comp (of p g)
  let z := fun i => f (coordinate p g i)
  have hz : ∀ i, b p * z i = b (g i) := by
    intro i
    change f (of p g p) * f (coordinate p g i) = f (of p g (g i))
    rw [← map_mul, of_mul_coordinate]
  have hp : IsRegular (b p) :=
    (IsLocalization.Away.algebraMap_isUnit (of p g p)).isRegular
  have hleft : ((awayForward p g).comp (toAway p g)).comp (of p g) = b := by
    apply RingHom.ext
    intro x
    change awayForward p g (toAway p g (of p g x)) = f (of p g x)
    rw [toAway_of, awayForward_base]
  exact (lift_unique p g b z hz hp _ hleft).trans
    (lift_unique p g b z hz hp f rfl).symm

/-- The fractional inverse is also a right inverse to the localized coefficient map. -/
theorem awayForward_comp_backward (p : B) (g : ι → B) :
    (awayForward p g).comp (awayBackward p g) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (of p g p))
  apply RingHom.ext
  intro x
  change awayForward p g (awayBackward p g
    ((@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance) x)) = _
  rw [awayBackward_base]
  exact DFunLike.congr_fun (awayForward_comp_toAway p g) x

/-- Inverting the distinguished element makes the actual modification isomorphic
 to the original ring with that element inverted. -/
def localizationAwayEquiv (p : B) (g : ι → B) :
    Localization.Away p ≃+* Localization.Away (M := Modification p g) (of p g p) where
  __ := awayForward p g
  invFun := awayBackward p g
  left_inv x := DFunLike.congr_fun (awayBackward_comp_forward p g) x
  right_inv x := DFunLike.congr_fun (awayForward_comp_backward p g) x

/-- The equivalence is induced by the original base map, not an abstract isomorphism. -/
@[simp] theorem localizationAwayEquiv_algebraMap (p : B) (g : ι → B) (b : B) :
    localizationAwayEquiv p g (algebraMap B (Localization.Away p) b) =
      (@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance) (of p g b) :=
  awayForward_base p g b

/-- The inverse equivalence also preserves the original coefficients. -/
@[simp] theorem localizationAwayEquiv_symm_of (p : B) (g : ι → B) (b : B) :
    (localizationAwayEquiv p g).symm
        ((@algebraMap (Modification p g)
        (Localization.Away (M := Modification p g) (of p g p))
        (inferInstance : CommSemiring (Modification p g))
        (inferInstance : Semiring (Localization.Away (M := Modification p g) (of p g p)))
        inferInstance) (of p g b)) =
      algebraMap B (Localization.Away p) b := by
  change awayBackward p g _ = _
  rw [awayBackward_base, toAway_of]

end Algebra.NeronModification
