/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatDVR.ComponentKernel
public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.ComponentStalk
public import Aglib.AlgebraicGeometry.Stalk.PrincipalBaseChange
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Actual special-fibre component kernels over a DVR

The original component immersion and the literal special-fibre projection
supply both stalk maps. Generic component minimality, the principal base-change
kernel calculation and surjective ideal correspondence prove the minimal-prime
statement. Flatness is used only to preserve the actual uniformizer as a
nonzerodivisor. The original universal family is supplied with no extra premise.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.FlatDVR

/-- The actual component-stalk kernel is minimal over the actual uniformizer ideal.
The minimal-prime assertion needs neither flatness nor Noetherianity. -/
theorem component_stalk_kernel_mem_minimalPrimes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X C : Scheme.{u}} [IsIntegral C] (π : X ⟶ Spec (.of R))
    (i : C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents
      (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u}))
    (ϖ : R) (hϖ : Irreducible ϖ) (c : C) :
    let j := i ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    RingHom.ker (j.stalkMap c).hom ∈
      (Ideal.span {stalkScalar π (j c) ϖ}).minimalPrimes := by
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let b : pullback π r ⟶ X := pullback.fst π r
  let : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hC := i.ker_stalkMap_mem_minimalPrimes_of_irreducibleComponent hi c
  have ht := Ideal.minimalPrimes_comap_of_surjective
    (f := (b.stalkMap (i c)).hom) (b.stalkMap_surjective (i c)) hC
  have hbase : RingHom.ker (IsLocalRing.residue R) = Ideal.span {ϖ} := by
    rw [IsLocalRing.ker_residue, hϖ.maximalIdeal_eq]
  have hb : RingHom.ker (b.stalkMap (i c)).hom =
      Ideal.span {π.stalkScalar (b (i c)) ϖ} :=
    Scheme.Hom.ker_stalkMap_pullback_fst_of_principal
      (IsLocalRing.residue R) IsLocalRing.residue_surjective ϖ hbase π (i c)
  rw [RingHom.comap_ker, ← RingHom.ker_eq_comap_bot, hb] at ht
  change RingHom.ker ((i ≫ b).stalkMap c).hom ∈
    (Ideal.span {π.stalkScalar (b (i c)) ϖ}).minimalPrimes
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.ker ((i.stalkMap c).hom.comp (b.stalkMap (i c)).hom) ∈ _
  exact ht

/-- The original universal flat-DVR component-kernel family, with its exact
maps, quantifiers and hypotheses, now has a proved native supplier. -/
theorem flatDVRFibreComponentKernel : FlatDVRFibreComponentKernel.{u} := by
  intro R _ _ _ X C _ _ π i ϖ hflat hclosed hi hϖ c
  let : Flat π := hflat
  let : IsClosedImmersion i := hclosed
  constructor
  · exact π.stalkScalar_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_iff_ne_zero.mpr hϖ.ne_zero)
  · exact component_stalk_kernel_mem_minimalPrimes π i hi ϖ hϖ c

end AlgebraicGeometry.Scheme.FlatDVR
