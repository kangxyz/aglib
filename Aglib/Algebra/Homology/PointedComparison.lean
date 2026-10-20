/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Group.NormalizedQuotient

/-!
# Conditional pointed comparison of additive maps

Lifting, extension, retraction, compatibility, annihilation and detection assumptions
remain independent inputs. The resulting equivalence is proved for the supplied
additive groups and homomorphisms.

Source: `lean/R5Lab/Aglib/Algebra/Homology/PointedComparison.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `4be363249528b9e5f02d6ec7cd1bc3c6fc04460b01151c1384929659d158f52f`.
-/

@[expose] public section

open AddMonoidHom.Retraction

namespace AddMonoidHom.PointedComparison

section Bockstein

variable {C D K H B V G L : Type*}
variable [AddCommGroup C] [AddCommGroup D] [AddCommGroup K] [AddCommGroup H] [AddCommGroup B]
variable [AddCommGroup V] [AddCommGroup G] [AddCommGroup L]
variable {I : AddSubgroup K}

/-- Pointed generic classes with integral Bockstein.
Source: the generic lifting argument in `K2-018#prop:k2018-arithmetic-characters`.
The arithmetic-surface realization by residue and purity is not included. -/
def integralPointed (origin : H →+ B) (bockstein : H →+ K) (I : AddSubgroup K) :
    AddSubgroup H := origin.ker ⊓ I.comap bockstein

/-- The integral pointed domain imposes the two source conditions independently. -/
@[simp] theorem mem_integralPointed (origin : H →+ B) (bockstein : H →+ K)
    (I : AddSubgroup K) (h : H) :
    h ∈ integralPointed origin bockstein I ↔ origin h = 0 ∧ bockstein h ∈ I := Iff.rfl

/-- The generic Bockstein restricted to `integralPointed`; integrality is in its domain. -/
def integralBockstein (origin : H →+ B) (bockstein : H →+ K) (I : AddSubgroup K) :
    integralPointed origin bockstein I →+ I where
  toFun := fun h => ⟨bockstein h, h.property.2⟩
  map_zero' := Subtype.ext (map_zero bockstein)
  map_add' := fun x y => Subtype.ext (map_add bockstein (x : H) (y : H))

/-- The integral Bockstein has the same generic-field value as the ambient map. -/
@[simp] theorem integralBockstein_coe (origin : H →+ B) (bockstein : H →+ K)
    (I : AddSubgroup K) (h : integralPointed origin bockstein I) :
    (integralBockstein origin bockstein I h : K) = bockstein h := rfl

/-- Specialization compatibility and coefficient annihilation give the normalized target.
Source: `K2-018#prop:k2018-arithmetic-characters`, lines 409–414.
Both compatibility and annihilation are explicit external premises. -/
def normalizedBockstein (origin : H →+ B) (bockstein : H →+ K) (I : AddSubgroup K)
    (s : I →+ C) (baseBockstein : B →+ D) (integralConstants : C →+ D)
    (integralConstantsInjective : Function.Injective integralConstants) (n : ℕ)
    (specialization : ∀ h (hi : bockstein h ∈ I),
      baseBockstein (origin h) = integralConstants (s ⟨bockstein h, hi⟩))
    (annihilated : ∀ h, n • bockstein h = 0) :
    integralPointed origin bockstein I →+ normalizedTorsion s n :=
  (integralBockstein origin bockstein I).codRestrict (normalizedTorsion s n) (by
    intro h
    constructor
    · apply integralConstantsInjective
      have hcompat := specialization h h.property.2
      have horigin : origin h = 0 := h.property.1
      simpa [integralBockstein, horigin] using hcompat.symm
    · apply AddSubgroup.torsionBy.nsmul_iff.mpr
      apply Subtype.ext
      exact annihilated h)

/-- Field lifting, horizontal extension, and specialization give a pointed lift.
Source: `K2-018#lem:k2018-residue-bockstein` and the first paragraph of
`K2-018#prop:k2018-arithmetic-characters`. The field and extension theorems,
origin section, and both naturality identities are independent premises. -/
theorem exists_pointed_lift (I : AddSubgroup K) (s : I →+ C)
    (integralConstants : C →+ D) (constants : D →+ K)
    (origin : H →+ B) (pullback : B →+ H) (hsection : Function.LeftInverse origin pullback)
    (restriction : H →+ V) (fieldBockstein : V →+ K) (baseBockstein : B →+ D)
    (n : ℕ)
    (fieldSurjective : ∀ k : K, n • k = 0 → ∃ v, fieldBockstein v = k)
    (horizontalExtension : ∀ v (x : I), fieldBockstein v = x →
      ∃ h, restriction h = v)
    (specialization : ∀ h (x : I), fieldBockstein (restriction h) = x →
      baseBockstein (origin h) = integralConstants (s x))
    (constantCompatibility : ∀ b,
      fieldBockstein (restriction (pullback b)) = constants (baseBockstein b))
    (x : I) (hx : s x = 0) (hn : n • x = 0) :
    ∃ h : origin.ker, fieldBockstein (restriction h) = x := by
  have hnK : n • (x : K) = 0 := congrArg Subtype.val hn
  obtain ⟨v, hv⟩ := fieldSurjective x hnK
  obtain ⟨h, hh⟩ := horizontalExtension v x hv
  have hδ : fieldBockstein (restriction h) = x := by rw [hh, hv]
  have hbase : baseBockstein (origin h) = 0 := by
    rw [specialization h x hδ, hx, map_zero]
  refine ⟨⟨normalize pullback origin h,
    specialize_normalize pullback origin hsection h⟩, ?_⟩
  change fieldBockstein (restriction (h - pullback (origin h))) = (x : K)
  rw [map_sub, map_sub, hδ, constantCompatibility, hbase, map_zero]
  simp

/-- The constructed pointed lift belongs to the integral generic subgroup by its image.
Source: the same generic lifting paragraph in `K2-018` as `exists_pointed_lift`. -/
theorem integralBockstein_exists_lift (I : AddSubgroup K) (s : I →+ C)
    (integralConstants : C →+ D) (constants : D →+ K)
    (origin : H →+ B) (pullback : B →+ H) (hsection : Function.LeftInverse origin pullback)
    (restriction : H →+ V) (fieldBockstein : V →+ K) (baseBockstein : B →+ D)
    (n : ℕ)
    (fieldSurjective : ∀ k : K, n • k = 0 → ∃ v, fieldBockstein v = k)
    (horizontalExtension : ∀ v (x : I), fieldBockstein v = x →
      ∃ h, restriction h = v)
    (specialization : ∀ h (x : I), fieldBockstein (restriction h) = x →
      baseBockstein (origin h) = integralConstants (s x))
    (constantCompatibility : ∀ b,
      fieldBockstein (restriction (pullback b)) = constants (baseBockstein b))
    (x : I) (hx : s x = 0) (hn : n • x = 0) :
    ∃ h : integralPointed origin (fieldBockstein.comp restriction) I,
      integralBockstein origin (fieldBockstein.comp restriction) I h = x := by
  obtain ⟨h, hh⟩ := exists_pointed_lift I s integralConstants constants origin pullback
    hsection restriction
    fieldBockstein baseBockstein n fieldSurjective horizontalExtension specialization
    constantCompatibility x hx hn
  refine ⟨⟨h, ⟨h.property, ?_⟩⟩, ?_⟩
  · change fieldBockstein (restriction h) ∈ I
    rw [hh]
    exact x.property
  · exact Subtype.ext hh

/-- Geometric restriction and geometric Bockstein detection imply pointed injectivity.
Source: `K2-018#eq:k2018-pointed-character`,
`K2-018#lem:k2018-geometric-exact-order`, and the second proof paragraph of
`K2-018#prop:k2018-arithmetic-characters`. These geometric inputs are premises;
field Bockstein surjectivity is not used for injectivity. -/
theorem injective_on_pointed_of_geometric_detection
    (origin : H →+ B) (bockstein : H →+ K) (geometricRestriction : H →+ G)
    (geometricBockstein : G →+ L) (geometricKRestriction : K →+ L)
    (pointedRestrictionDetects : ∀ h, origin h = 0 → geometricRestriction h = 0 → h = 0)
    (geometricBocksteinDetects : ∀ g, geometricBockstein g = 0 → g = 0)
    (geometricCompatibility : ∀ h,
      geometricBockstein (geometricRestriction h) = geometricKRestriction (bockstein h)) :
    Function.Injective (bockstein.domRestrict origin.ker) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro h hh
  apply Subtype.ext
  apply pointedRestrictionDetects h h.property
  apply geometricBocksteinDetects
  rw [geometricCompatibility]
  change bockstein (h : H) = 0 at hh
  rw [hh, map_zero]

/-- Pointed injectivity restricts to integral classes; generic support for `K2-018`. -/
theorem integralBockstein_injective (origin : H →+ B) (bockstein : H →+ K)
    (I : AddSubgroup K) (h : Function.Injective (bockstein.domRestrict origin.ker)) :
    Function.Injective (integralBockstein origin bockstein I) := by
  intro x y hxy
  apply Subtype.ext
  have hx : (⟨x, x.property.1⟩ : origin.ker) = ⟨y, y.property.1⟩ :=
    h (congrArg Subtype.val hxy)
  exact congrArg (fun z : origin.ker => (z : H)) hx

/-- Pointed injectivity preserves every scalar annihilator, the algebra behind exact order.
Source: the injectivity and exact-order conclusion in `K2-018#prop:k2018-arithmetic-characters`.
The injectivity premise is supplied by `injective_on_pointed_of_geometric_detection`. -/
theorem pointedBockstein_preserves_annihilator (origin : H →+ B) (bockstein : H →+ K)
    (hinj : Function.Injective (bockstein.domRestrict origin.ker))
    (h : origin.ker) (m : ℕ) :
    m • bockstein h = 0 ↔ m • h = 0 := by
  constructor
  · intro hm
    apply hinj
    change bockstein (m • (h : H)) = bockstein (0 : H)
    rw [map_nsmul, hm, map_zero]
  · intro hm
    have hzero : m • (h : H) = 0 := congrArg Subtype.val hm
    rw [← map_nsmul, hzero, map_zero]

/-- Conditional assembly of the integral generic character comparison.
Source: `K2-018#prop:k2018-arithmetic-characters`, lines 409–424, restricted
to the generic comparison. Its field, horizontal, specialization, coefficient,
and geometric inputs are explicit, and bijectivity is proved from them.
Compose with `normalizedTorsionQuotientEquiv` after supplying the additional
constant-retraction identity to obtain the reduced-quotient formulation.
No identification with actual étale or K-theory groups, or with `H¹(X_ℓ)`,
is asserted by this declaration. -/
noncomputable def integralPointedEquivNormalizedTorsion (I : AddSubgroup K) (s : I →+ C)
    (integralConstants : C →+ D) (integralConstantsInjective : Function.Injective integralConstants)
    (constants : D →+ K)
    (origin : H →+ B) (pullback : B →+ H) (hsection : Function.LeftInverse origin pullback)
    (restriction : H →+ V) (fieldBockstein : V →+ K) (baseBockstein : B →+ D)
    (n : ℕ)
    (fieldSurjective : ∀ k : K, n • k = 0 → ∃ v, fieldBockstein v = k)
    (horizontalExtension : ∀ v (x : I), fieldBockstein v = x →
      ∃ h, restriction h = v)
    (specialization : ∀ h (x : I), fieldBockstein (restriction h) = x →
      baseBockstein (origin h) = integralConstants (s x))
    (constantCompatibility : ∀ b,
      fieldBockstein (restriction (pullback b)) = constants (baseBockstein b))
    (annihilated : ∀ v, n • fieldBockstein v = 0)
    (geometricRestriction : H →+ G) (geometricBockstein : G →+ L)
    (geometricKRestriction : K →+ L)
    (pointedRestrictionDetects : ∀ h, origin h = 0 → geometricRestriction h = 0 → h = 0)
    (geometricBocksteinDetects : ∀ g, geometricBockstein g = 0 → g = 0)
    (geometricCompatibility : ∀ h, geometricBockstein (geometricRestriction h) =
      geometricKRestriction (fieldBockstein (restriction h))) :
    integralPointed origin (fieldBockstein.comp restriction) I ≃+ normalizedTorsion s n :=
  AddEquiv.ofBijective (normalizedBockstein origin (fieldBockstein.comp restriction) I s
    baseBockstein integralConstants integralConstantsInjective n
    (fun h hi => specialization h ⟨fieldBockstein (restriction h), hi⟩ rfl)
    (fun h => annihilated (restriction h))) (by
      constructor
      · intro x y hxy
        apply integralBockstein_injective origin (fieldBockstein.comp restriction) I
          (injective_on_pointed_of_geometric_detection origin (fieldBockstein.comp restriction)
            geometricRestriction geometricBockstein geometricKRestriction
            pointedRestrictionDetects geometricBocksteinDetects geometricCompatibility)
        exact congrArg Subtype.val hxy
      · intro x
        obtain ⟨h, hh⟩ := integralBockstein_exists_lift I s integralConstants constants origin
          pullback hsection restriction
          fieldBockstein baseBockstein n fieldSurjective horizontalExtension specialization
          constantCompatibility x x.property.1
            (AddSubgroup.torsionBy.nsmul_iff.mp x.property.2)
        exact ⟨h, Subtype.ext hh⟩)

end Bockstein

end AddMonoidHom.PointedComparison
