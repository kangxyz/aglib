/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.HorizontalGenerization
public import Aglib.RingTheory.KrullDimension.PrincipalOpen

/-!
# Dedekind-base local dimension from horizontal stalk bounds

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.DedekindDimension`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `2f0c4d567939ef186c377a33fcb188be26b2b593e736335bcf92e187c2082db9`, selected lines [[36,
114]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace AlgebraicGeometry.Scheme.DedekindBase
variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  {X : Scheme.{u}} [IsIntegral X]

omit [IsDedekindDomain A] [IsIntegral X] in
/-- Contraction of the source maximal ideal is exactly the point's base prime. -/
theorem baseToStalk_comap_maximalIdeal (f : X ⟶ Spec (.of A)) (x : X) :
    (maximalIdeal (X.presheaf.stalk x)).comap (DedekindBase.baseToStalk f x) =
      (f x).asIdeal := by
  change ((maximalIdeal (X.presheaf.stalk x)).comap (f.stalkMap x).hom).comap
    (StructureSheaf.toStalk A (f x)).hom = _
  rw [IsLocalRing.maximalIdeal_comap]
  let : (f x).asIdeal.IsPrime := (f x).isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra A (f x)
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (f x)) (f x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (f x)
  exact IsLocalization.AtPrime.under_maximalIdeal _ _

-- Retain the specified fraction-field model of the source horizontal-stalk interface.
/-- Horizontal stalk dimension at most one bounds every stalk dimension by two.
Local Noetherianity is derived from the displayed locally-finite-type morphism. -/
@[nolint unusedArguments]
theorem stalk_dimension_le_two_of_horizontal_stalk_le_one
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [IsDominant f]
    (hh : ∀ y : X, f y = genericPoint (Spec (.of A)) →
      ringKrullDim (X.presheaf.stalk y) ≤ 1) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_cases hpx : (f x).asIdeal = ⊥
  · exact (hh x ((DedekindBase.image_eq_genericPoint_iff f x).mpr hpx)).trans (by norm_num)
  obtain ⟨a, hap, ha0⟩ := (f x).asIdeal.ne_bot_iff.mp hpx
  let t := DedekindBase.baseToStalk f x a
  have ht : t ≠ 0 := by
    simpa [t] using (baseToStalk_injective f x).ne ha0
  apply _root_.IsLocalRing.ringKrullDim_le_two_of_principal_open_height_le_one t ht
  intro P hP htP
  let : P.IsPrime := hP
  let q : Ideal A := P.comap (DedekindBase.baseToStalk f x)
  have hqp : q ≤ (f x).asIdeal := by
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime P)).trans_eq
      (baseToStalk_comap_maximalIdeal f x)
  have hq : q = ⊥ := by
    by_contra hq
    have hqm : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq
    have he : q = (f x).asIdeal := hqm.eq_of_le (f x).isPrime.ne_top hqp
    have haq : a ∈ q := he.symm ▸ hap
    exact htP haq
  let z : Spec (X.presheaf.stalk x) := ⟨P, hP⟩
  let j := X.fromSpecStalk x
  let y : X := j z
  have hy : f y = genericPoint (Spec (.of A)) := by
    apply (DedekindBase.image_eq_genericPoint_iff f y).mpr
    change (f y).asIdeal = ⊥
    have he : (f y).asIdeal = q := by
      change ((X.fromSpecStalk x ≫ f) z).asIdeal = q
      rw [fromSpecStalk_comp_eq]
      rfl
    exact he.trans hq
  have hd := hh y hy
  let : Flat j := _root_.AlgebraicGeometry.Scheme.fromSpecStalk_flat X x
  let : IsIso (j.stalkMap z) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks j z
  let e := (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv
  change ringKrullDim (X.presheaf.stalk (j z)) ≤ 1 at hd
  rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_stalk_eq_coheight,
    ← idealHeight_eq_coheight (X.presheaf.stalk x) z] at hd
  exact WithBot.coe_le_coe.mp hd

end AlgebraicGeometry.Scheme.DedekindBase
