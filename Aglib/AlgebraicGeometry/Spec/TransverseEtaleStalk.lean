/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.EtaleLocalBase
public import Aglib.AlgebraicGeometry.Stalk.SpecLocalRing
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The actual transverse stalk of an étale chart

The only extension ring is the stalk at an actual point of the original
pullback. Both original scalar routes agree, without a map from the chart
base to the original DVR.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Pulling an actual étale chart back along a transverse section gives a native
DVR stalk. Its chart scalars and its original DVR scalars retain the whole
original base square. -/
theorem exists_transverseEtaleStalk
    (R A D : Type u) [CommRing R] [CommRing A] [CommRing D]
    [Algebra R A] [Algebra R D] [IsDomain D] [IsDiscreteValuationRing D]
    {W Z : Scheme.{u}} (π : W ⟶ Z) [Etale π]
    (c : W ⟶ Spec (.of A)) (p : Z ⟶ Spec (.of R))
    (hc : π ≫ p = c ≫ Spec.algebraMap R A)
    (s : Spec (.of D) ⟶ Z) (hs : s ≫ p = Spec.algebraMap R D)
    (y : W) (hy : π y = s (IsLocalRing.closedPoint D))
    {t : D} (ht : Irreducible t) :
    ∃ z : (pullback π s : Scheme),
      (pullback.fst π s : pullback π s ⟶ W) z = y ∧
      (pullback.snd π s : pullback π s ⟶ Spec (.of D)) z =
        IsLocalRing.closedPoint D ∧
      ∃ hD : IsDomain ((pullback π s).presheaf.stalk z),
      letI := hD
      IsDiscreteValuationRing ((pullback π s).presheaf.stalk z) ∧
      Irreducible ((pullback.snd π s).stalkScalar z t) ∧
      ∃ a : A →+* (pullback π s).presheaf.stalk z,
        Spec.map (CommRingCat.ofHom a) =
          (pullback π s).fromSpecStalk z ≫ pullback.fst π s ≫ c ∧
        a.comp (algebraMap R A) =
          ((pullback.snd π s).stalkScalar z).comp (algebraMap R D) ∧
        ((pullback π s).fromSpecStalk z ≫ pullback.fst π s) ≫ π =
          Spec.map (CommRingCat.ofHom ((pullback.snd π s).stalkScalar z)) ≫ s ∧
        ((pullback π s).fromSpecStalk z ≫ pullback.fst π s)
          (IsLocalRing.closedPoint ((pullback π s).presheaf.stalk z)) = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Pullback.exists_preimage_pullback (f := π) (g := s) y
    (IsLocalRing.closedPoint D) hy
  have hdvr := Hom.stalkScalar_dvr_uniformizer (pullback.snd π s) z hz₂ ht
  obtain ⟨hD, hdvr, ht'⟩ := hdvr
  let := hD
  let η := (pullback π s).fromSpecStalk z ≫ pullback.fst π s
  have hη : η ≫ π =
      Spec.map (CommRingCat.ofHom ((pullback.snd π s).stalkScalar z)) ≫ s := by
    dsimp [η]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      fromSpecStalk_comp_eq_spec_map_stalkScalar]
  obtain ⟨a, ha⟩ := Spec.map_surjective (η ≫ c)
  refine ⟨z, hz₁, hz₂, hD, hdvr, ht', a.hom, ha, ?_, hη, ?_⟩
  · have hmap :
        Spec.map (CommRingCat.ofHom (algebraMap R A) ≫ a) =
          Spec.map (CommRingCat.ofHom (algebraMap R D) ≫
            CommRingCat.ofHom ((pullback.snd π s).stalkScalar z)) := by
      rw [Spec.map_comp, Spec.map_comp, ha, Category.assoc, ← hc,
        ← Category.assoc, hη, Category.assoc, hs]
    have hcomp := Spec.map_injective hmap
    ext r
    exact ConcreteCategory.congr_hom hcomp r
  · change (pullback.fst π s : pullback π s ⟶ W)
      ((pullback π s).fromSpecStalk z
        (IsLocalRing.closedPoint ((pullback π s).presheaf.stalk z))) = y
    rw [fromSpecStalk_closedPoint]
    exact hz₁

end AlgebraicGeometry.Scheme
