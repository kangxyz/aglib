/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericPoint
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Regular
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.Topology.KrullDimension.ClosedEmbedding
public import Mathlib.RingTheory.Ideal.Height

/-!
# Actual Cartier ideals from global codimension one

The actual stalk-map kernel is the prime whose image under the original
local-spectrum map is the image of the source generic point. Comparing
specialization chains along that embedding bounds its prime height. For
integral source and target, generic coheight one therefore gives height-one
stalk kernels at every source point.

Consequently an integral proper closed subspace of dimension n in an
integral regular locally Noetherian scheme of dimension at most n+1 is an
actual effective Cartier divisor. No global-purity or catenarity assertion
is substituted for the original stalk-map calculation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]

/-- Generic codimension one controls the height of the original stalk-map
kernel. The map itself need not be a closed immersion for this statement. -/
theorem stalkMap_ker_height_eq_one_of_generic_coheight (i : C ⟶ Y)
    (hcodim : @Order.coheight Y (specializationOrder Y).toPreorder
      (i (genericPoint C)) = 1) (c : C) :
    (RingHom.ker (i.stalkMap c).hom).height = 1 := by
  let : PartialOrder Y := specializationOrder Y
  let R := Y.presheaf.stalk (i c)
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (i.stalkMap c).hom (⊥ : PrimeSpectrum (C.presheaf.stalk c))
  have hpker : p.asIdeal = RingHom.ker (i.stalkMap c).hom := rfl
  have hp : Y.fromSpecStalk (i c) p = i (genericPoint C) := by
    have h := congrArg
      (fun q : Spec (C.presheaf.stalk c) ⟶ Y =>
        q (⊥ : PrimeSpectrum (C.presheaf.stalk c)))
      (Scheme.SpecMap_stalkMap_fromSpecStalk i (x := c))
    change Y.fromSpecStalk (i c) p =
      i (C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))) at h
    simpa only [Scheme.fromSpecStalk_bot c] using h
  have hstrict : StrictMono
      (fun q : (PrimeSpectrum R)ᵒᵈ => Y.fromSpecStalk (i c) q) := by
    intro a b hab
    refine lt_of_le_of_ne ?_ ?_
    · exact ((PrimeSpectrum.le_iff_specializes b a).mp hab.le).map
        (Y.fromSpecStalk (i c)).continuous
    · intro heq
      exact hab.ne ((Y.fromSpecStalk (i c)).isEmbedding.injective heq)
  have hheight : p.asIdeal.height ≤ Order.coheight (i (genericPoint C)) := by
    rw [PrimeSpectrum.height_eq_orderHeight]
    have h := Order.coheight_le_coheight_apply_of_strictMono
      (fun q : (PrimeSpectrum R)ᵒᵈ => Y.fromSpecStalk (i c) q) hstrict p
    change Order.height p ≤ Order.coheight (Y.fromSpecStalk (i c) p) at h
    simpa only [hp] using h
  have hle : (RingHom.ker (i.stalkMap c).hom).height ≤ 1 := by
    rw [← hpker]
    exact hheight.trans_eq hcodim
  have hne : RingHom.ker (i.stalkMap c).hom ≠ ⊥ := by
    intro hzero
    have hpzero : p = ⊥ := PrimeSpectrum.ext (hpker.trans hzero)
    have hgeneric : i (genericPoint C) = genericPoint Y :=
      hp.symm.trans (by rw [hpzero]; exact Scheme.fromSpecStalk_bot (i c))
    have hmax : IsMax (i (genericPoint C)) := by
      rw [hgeneric]
      intro y _
      exact genericPoint_specializes y
    have hc0 := Order.coheight_eq_zero.mpr hmax
    exact one_ne_zero (hcodim.symm.trans hc0)
  have hge : 1 ≤ (RingHom.ker (i.stalkMap c).hom).height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hne)
  exact le_antisymm hle hge

/-- A proper integral closed image of dimension n inside an integral regular
locally Noetherian ambient scheme of dimension at most n+1 is an actual
effective Cartier divisor, using its original kernel ideal. -/
theorem isEffectiveCartier_of_dimension [IsLocallyNoetherian Y]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (n : ℕ) (hC : topologicalKrullDim C = n)
    (hY : topologicalKrullDim Y ≤ (n : WithBot ℕ∞) + 1)
    (hrange : Set.range i ≠ Set.univ) : IsEffectiveCartier i := by
  let : PartialOrder Y := specializationOrder Y
  have hcodim : Order.coheight (i (genericPoint C)) = 1 :=
    TopologicalSpace.coheight_image_genericPoint_eq_one i i.isClosedEmbedding n hC hY hrange
  exact ⟨inferInstance, idealModule_isLocallyRankOne_of_regularStalks i hregular
    (stalkMap_ker_height_eq_one_of_generic_coheight i hcodim)⟩

end AlgebraicGeometry.Scheme.Hom
