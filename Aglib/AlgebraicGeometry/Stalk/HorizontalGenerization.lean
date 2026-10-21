/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DedekindBase
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.RingTheory.KrullDimension.HeightOnePrime

/-!
# Horizontal codimension-one generizations from actual stalk primes

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.HorizontalGenerization`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `87dbbd6d7cd3403be57e4ee7dc7b01018cf2f445e4e0a85505ff2dc921972437`, selected lines [[31,
134]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.DedekindBase

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]

/-- Dominance makes the literal base-to-stalk map injective. -/
theorem baseToStalk_injective (x : X) : Function.Injective (baseToStalk f x) := by
  intro a b hab
  apply IsFractionRing.injective A (FractionRing A)
  apply (constantToFunctionField (FractionRing A) f).injective
  rw [constantToFunctionField_algebraMap (FractionRing A) f x,
    constantToFunctionField_algebraMap (FractionRing A) f x, hab]

/-- The actual map from the localized base into the model stalk is injective. -/
theorem localizationToStalk_injective (x : X) :
    Function.Injective (localizationToStalk f x) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (imagePrime f x).asIdeal.primeCompl (localizationToStalk f x)).mpr
  intro a b
  rw [localizationToStalk_algebraMap, localizationToStalk_algebraMap]
  exact (IsLocalization.injective (Localization.AtPrime (imagePrime f x).asIdeal)
    (imagePrime f x).asIdeal.primeCompl_le_nonZeroDivisors).eq_iff.trans
      (baseToStalk_injective f x).eq_iff.symm

omit [IsDedekindDomain A] [IsIntegral X] [IsDominant f] in
/-- The local-spectrum structural triangle uses the original scheme morphism. -/
theorem fromSpecStalk_comp_eq (x : X) :
    X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (baseToStalk f x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

end AlgebraicGeometry.Scheme.DedekindBase

namespace AlgebraicGeometry.Scheme.CodimensionOnePoint
variable {X : Scheme.{u}}

/-- A height-one prime of the original stalk produces a codimension-one point
using exactly `Scheme.fromSpecStalk`. -/
def ofStalkPrime (x : X) (q : Ideal (X.presheaf.stalk x))
    [q.IsPrime] (hq : q.height = 1) : CodimensionOnePoint X := by
  let z : Spec (X.presheaf.stalk x) := ⟨q, inferInstance⟩
  letI : Flat (X.fromSpecStalk x) :=
    _root_.AlgebraicGeometry.Scheme.fromSpecStalk_flat X x
  let : IsIso ((X.fromSpecStalk x).stalkMap z) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks (X.fromSpecStalk x) z
  refine ⟨X.fromSpecStalk x z, ?_⟩
  calc
    ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x z)) =
        ringKrullDim ((Spec (X.presheaf.stalk x)).presheaf.stalk z) :=
      ringKrullDim_eq_of_ringEquiv
        (asIso ((X.fromSpecStalk x).stalkMap z)).commRingCatIsoToRingEquiv
    _ = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
      exact_mod_cast hq

/-- The point constructed from a stalk prime specializes to the original point. -/
theorem ofStalkPrime_specializes (x : X)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime] (hq : q.height = 1) :
    (ofStalkPrime x q hq).1 ⤳ x := by
  apply (show Set.range (X.fromSpecStalk x) = {y | y ⤳ x}
    from Scheme.range_fromSpecStalk).le
  exact ⟨⟨q, inferInstance⟩, rfl⟩

end AlgebraicGeometry.Scheme.CodimensionOnePoint

namespace AlgebraicGeometry.Scheme.DedekindBase
variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]

/-- Over a nonzero prime of a Dedekind base, every stalk of dimension at least
two has an actual horizontal codimension-one generization. -/
theorem exists_horizontal_codimensionOne_generization
    [IsLocallyNoetherian X] (x : X)
    (hdim : 1 < ringKrullDim (X.presheaf.stalk x))
    (hx : (imagePrime f x).asIdeal ≠ ⊥) :
    ∃ d : CodimensionOnePoint X,
      f d.1 = genericPoint (Spec (CommRingCat.of A)) ∧ d.1 ⤳ x := by
  let B := Localization.AtPrime (imagePrime f x).asIdeal
  let v : B →+* X.presheaf.stalk x := localizationToStalk f x
  let : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hx B
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hv : Function.Injective v := localizationToStalk_injective f x
  have hvπ : v π ≠ 0 := by
    exact (map_ne_zero_iff v hv).mpr hπ.ne_zero
  have hvπunit : ¬ IsUnit (v π) := by
    exact fun h => hπ.not_isUnit (IsLocalHom.map_nonunit (f := v) π h)
  obtain ⟨q, hqprime, hqheight, hπq⟩ :=
    _root_.IsLocalRing.exists_heightOne_prime_not_mem (X.presheaf.stalk x)
      hdim (v π) hvπ hvπunit
  let : q.IsPrime := hqprime
  have hcomap : q.comap v = ⊥ := by
    by_contra hn
    have hpmax : (q.comap v).IsMaximal :=
      (Ideal.comap_isPrime v q).isMaximal_of_ne_bot hn
    have hEq : q.comap v = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal hpmax
    apply hπq
    change π ∈ q.comap v
    rw [hEq]
    exact hπ.not_isUnit
  have hbase : q.comap (baseToStalk f x) = ⊥ := by
    have hm : baseToStalk f x = v.comp (algebraMap A B) := by
      ext a
      exact (localizationToStalk_algebraMap f x a).symm
    rw [hm, ← Ideal.comap_comap, hcomap]
    exact Ideal.comap_bot_of_injective _
      (IsLocalization.injective B (imagePrime f x).asIdeal.primeCompl_le_nonZeroDivisors)
  refine ⟨CodimensionOnePoint.ofStalkPrime x q hqheight, ?_,
    CodimensionOnePoint.ofStalkPrime_specializes x q hqheight⟩
  apply (image_eq_genericPoint_iff f _).mpr
  change (f (X.fromSpecStalk x ⟨q, hqprime⟩)).asIdeal = ⊥
  have heq := congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ Spec (CommRingCat.of A) =>
    g (⟨q, hqprime⟩ : Spec (X.presheaf.stalk x))) (fromSpecStalk_comp_eq f x)
  change f (X.fromSpecStalk x ⟨q, hqprime⟩) =
    PrimeSpectrum.comap (baseToStalk f x) ⟨q, hqprime⟩ at heq
  rw [heq]
  exact hbase

end AlgebraicGeometry.Scheme.DedekindBase
