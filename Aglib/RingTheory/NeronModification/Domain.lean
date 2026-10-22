/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Away
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Injectivity and domain stability of the actual Néron modification

The modification embeds in the original away localization. In particular a
nonzero distinguished element in a domain gives another domain. Injective
actual points remain injective after the specified divisibility lift.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Algebra.NeronModification

variable {B C ι : Type*} [CommRing B] [CommRing C]
variable (p : B) (g : ι → B)

/-- The actual map to the original away localization is injective, even when
`p` is a zero divisor or the modification is the zero ring. -/
theorem toAway_injective : Function.Injective (toAway p g) := by
  have hM : Submonoid.powers (of p g p) ≤ nonZeroDivisors (Modification p g) :=
    Submonoid.powers_le.mpr (isRegular_of p g).mem_nonZeroDivisors
  have hi := IsLocalization.injective (R := Modification p g)
    (M := Submonoid.powers (of p g p))
    (Localization.Away (M := Modification p g) (of p g p)) hM
  intro x y hxy
  apply hi
  calc
    algebraMap (Modification p g) (Localization.Away (M := Modification p g) (of p g p)) x =
      awayForward p g (toAway p g x) := (DFunLike.congr_fun
        (awayForward_comp_toAway p g) x).symm
    _ = awayForward p g (toAway p g y) := congrArg (awayForward p g) hxy
    _ = algebraMap (Modification p g)
      (Localization.Away (M := Modification p g) (of p g p)) y :=
        DFunLike.congr_fun (awayForward_comp_toAway p g) y

/-- A domain remains a domain after modification at a nonzero element.
Nonzeroness is essential: modification at zero is the zero ring. -/
theorem isDomain_modification [IsDomain B] (hp : p ≠ 0) : IsDomain (Modification p g) := by
  let : IsDomain (Localization.Away p) := Localization.Away.isDomain hp
  exact Function.Injective.isDomain (toAway p g) (toAway_injective p g)

/-- Localizing an actual lifted point agrees with the original fractional point. -/
theorem awayMap_comp_toAway (f : B →+* C) (z : ι → C)
    (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p)) :
    (Localization.awayMap f p).comp (toAway p g) =
      (algebraMap C (Localization.Away (f p))).comp (lift p g f z hz hp) := by
  let a := algebraMap C (Localization.Away (f p))
  let c := a.comp f
  let w := fun i => a (z i)
  have hc : IsRegular (c p) := (IsLocalization.Away.algebraMap_isUnit (f p)).isRegular
  have hw (i : ι) : c p * w i = c (g i) := by
    change a (f p) * a (z i) = a (f (g i))
    rw [← map_mul, hz]
  apply (lift_unique p g c w hw hc _ ?_).trans (lift_unique p g c w hw hc _ ?_).symm
  · ext b
    change Localization.awayMap f p (toAway p g (of p g b)) = a (f b)
    simp only [toAway, lift_of, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  · ext b
    change a (lift p g f z hz hp (of p g b)) = a (f b)
    rw [lift_of]

/-- An injective original point remains injective under its actual modification lift. -/
theorem lift_injective (f : B →+* C) (hf : Function.Injective f) (z : ι → C)
    (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p)) :
    Function.Injective (lift p g f z hz hp) := by
  have hloc : Function.Injective (Localization.awayMap f p) := by
    apply Localization.awayMap_injective_iff.mpr
    intro b hb
    have hb₀ : b = 0 := hf (hb.trans (map_zero f).symm)
    exact ⟨0, by rw [hb₀, mul_zero]⟩
  intro x y hxy
  apply toAway_injective p g
  apply hloc
  calc
    Localization.awayMap f p (toAway p g x) =
      algebraMap C (Localization.Away (f p)) (lift p g f z hz hp x) :=
        DFunLike.congr_fun (awayMap_comp_toAway p g f z hz hp) x
    _ = algebraMap C (Localization.Away (f p)) (lift p g f z hz hp y) :=
        congrArg (algebraMap C (Localization.Away (f p))) hxy
    _ = Localization.awayMap f p (toAway p g y) :=
        (DFunLike.congr_fun (awayMap_comp_toAway p g f z hz hp) y).symm

end Algebra.NeronModification
