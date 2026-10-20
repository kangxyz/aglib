/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Lifting the actual saturated affine chart

Regularity of the image of the distinguished denominator and divisibility of
the image ideal construct a unique algebra map from the existing subalgebra
of the actual principal localization. No scheme universal property is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

namespace Localization.Away.SaturatedChart
variable {A : Type u} [CommRing A] (I : Ideal A) (a : I)

/-- The original fraction, regarded as an element of the existing saturated chart. -/
def fractionElement (b : I) : saturatedChart A I (a : A) :=
  ⟨fraction (a : A) (b : A), fraction_mem I (a : A) (b : A) b.property⟩

theorem fractionElement_mul (b : I) :
    algebraMap A (saturatedChart A I (a : A)) (a : A) * fractionElement I a b =
      algebraMap A (saturatedChart A I (a : A)) (b : A) := by
  apply Subtype.ext
  change algebraMap A (Localization.Away (a : A)) (a : A) *
    fraction (a : A) (b : A) = _
  rw [mul_comm, fraction_mul_self]
  exact ((saturatedChart A I (a : A)).val.commutes (b : A)).symm

section Algebra
variable {S : Type v} [CommRing S] [Algebra A S]

/-- Every actual algebra map obeys the original fraction equation. -/
theorem algHom_fraction_mul (g : saturatedChart A I (a : A) →ₐ[A] S) (b : I) :
    algebraMap A S (a : A) * g (fractionElement I a b) = algebraMap A S (b : A) := by
  have h := congrArg g (fractionElement_mul I a b)
  simpa only [map_mul, AlgHom.commutes] using h

/-- Regularity forces any two actual chart algebra maps to agree. -/
theorem algHom_ext (hreg : IsRegular (algebraMap A S (a : A)))
    (g h : saturatedChart A I (a : A) →ₐ[A] S) : g = h := by
  apply AlgHom.adjoin_ext
  rintro z ⟨b, hb, rfl⟩
  change g (fractionElement I a ⟨b, hb⟩) = h (fractionElement I a ⟨b, hb⟩)
  exact hreg.left ((algHom_fraction_mul I a g ⟨b, hb⟩).trans
    (algHom_fraction_mul I a h ⟨b, hb⟩).symm)

/-- The actual localization map carries the entire chart into the scalar-map range.
Inverting that range embedding constructs the original algebra lift. -/
theorem exists_algHom_of_regular
    (hreg : IsRegular (algebraMap A S (a : A)))
    (hdiv : ∀ b : I, algebraMap A S (a : A) ∣ algebraMap A S (b : A)) :
    ∃ g : saturatedChart A I (a : A) →ₐ[A] S,
      (algebraMap S (Localization.Away (algebraMap A S (a : A)))).comp g.toRingHom =
        (Localization.awayMap (algebraMap A S) (a : A)).comp
          (saturatedChart A I (a : A)).val.toRingHom := by
  let L := Localization.Away (algebraMap A S (a : A))
  let F : Localization.Away (a : A) →ₐ[A] L := {
    toRingHom := Localization.awayMap (algebraMap A S) (a : A)
    commutes' := fun x => by
      change Localization.awayMap (algebraMap A S) (a : A)
        (algebraMap A (Localization.Away (a : A)) x) = algebraMap A L x
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      exact (IsScalarTower.algebraMap_apply A S L x).symm }
  let j : S →ₐ[A] L := IsScalarTower.toAlgHom A S L
  have hj : Function.Injective j := by
    change Function.Injective (algebraMap S L)
    exact IsLocalization.injective L (Submonoid.powers_le.mpr hreg.mem_nonZeroDivisors)
  have hF (x : A) : F (algebraMap A (Localization.Away (a : A)) x) =
      j (algebraMap A S x) :=
    (F.commutes x).trans (IsScalarTower.algebraMap_apply A S L x)
  have hinv : F (IsLocalization.Away.invSelf (a : A)) =
      IsLocalization.Away.invSelf (algebraMap A S (a : A)) := by
    apply map_invSelf_of_mul (a : A) F.toRingHom
    change F (algebraMap A (Localization.Away (a : A)) (a : A)) *
      IsLocalization.Away.invSelf (algebraMap A S (a : A)) = 1
    rw [hF]
    exact IsLocalization.Away.mul_invSelf (algebraMap A S (a : A))
  have hC : saturatedChart A I (a : A) ≤ j.range.comap F := by
    apply Algebra.adjoin_le
    rintro z ⟨b, hb, rfl⟩
    obtain ⟨q, hq⟩ := hdiv ⟨b, hb⟩
    change ∃ q : S, j q = F (algebraMap A (Localization.Away (a : A)) b *
      IsLocalization.Away.invSelf (a : A))
    refine ⟨q, ?_⟩
    rw [map_mul, hF, hinv, hq, map_mul]
    symm
    calc
      (j (algebraMap A S (a : A)) * j q) *
          IsLocalization.Away.invSelf (algebraMap A S (a : A)) =
        j q * (algebraMap S L (algebraMap A S (a : A)) *
          IsLocalization.Away.invSelf (algebraMap A S (a : A))) := by
            change (algebraMap S L _ * j q) * _ = _
            ring
      _ = j q := by rw [IsLocalization.Away.mul_invSelf, mul_one]
  let p : saturatedChart A I (a : A) →ₐ[A] j.range :=
    (F.comp (saturatedChart A I (a : A)).val).codRestrict j.range
      (fun z => hC z.property)
  let e : S ≃ₐ[A] j.range := AlgEquiv.ofInjective j hj
  let g := e.symm.toAlgHom.comp p
  refine ⟨g, ?_⟩
  ext z
  change j (e.symm (p z)) = F z.val
  exact congrArg Subtype.val (e.apply_symm_apply (p z))

/-- The actual lift obtained by the proved range construction. -/
def lift (hreg : IsRegular (algebraMap A S (a : A)))
    (hdiv : ∀ b : I, algebraMap A S (a : A) ∣ algebraMap A S (b : A)) :
    saturatedChart A I (a : A) →ₐ[A] S :=
  (exists_algHom_of_regular I a hreg hdiv).choose

/-- The lift retains the exact map between the two actual localizations. -/
theorem lift_localizationTriangle (hreg : IsRegular (algebraMap A S (a : A)))
    (hdiv : ∀ b : I, algebraMap A S (a : A) ∣ algebraMap A S (b : A)) :
    (algebraMap S (Localization.Away (algebraMap A S (a : A)))).comp
        (lift I a hreg hdiv).toRingHom =
      (Localization.awayMap (algebraMap A S) (a : A)).comp
        (saturatedChart A I (a : A)).val.toRingHom :=
  (exists_algHom_of_regular I a hreg hdiv).choose_spec

/-- The value on the original fraction is its unique quotient in the target ring. -/
theorem lift_fraction_eq (hreg : IsRegular (algebraMap A S (a : A)))
    (hdiv : ∀ b : I, algebraMap A S (a : A) ∣ algebraMap A S (b : A))
    (b : I) (q : S) (hq : algebraMap A S (a : A) * q = algebraMap A S (b : A)) :
    lift I a hreg hdiv (fractionElement I a b) = q :=
  hreg.left ((algHom_fraction_mul I a (lift I a hreg hdiv) b).trans hq.symm)

/-- The unique actual algebra map sends every original fraction to its quotient. -/
theorem existsUnique_algHom (hreg : IsRegular (algebraMap A S (a : A)))
    (hdiv : ∀ b : I, algebraMap A S (a : A) ∣ algebraMap A S (b : A)) :
    ∃! g : saturatedChart A I (a : A) →ₐ[A] S,
      ∀ b : I, algebraMap A S (a : A) * g (fractionElement I a b) =
        algebraMap A S (b : A) := by
  refine ⟨lift I a hreg hdiv, algHom_fraction_mul I a _, ?_⟩
  intro g _
  exact algHom_ext I a hreg g (lift I a hreg hdiv)

end Algebra

section RingHom
variable {S : Type v} [CommRing S]

/-- The algebra structure on the target is exactly the one supplied by the actual `f`. -/
def liftOfHom (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) :
    letI : Algebra A S := f.toAlgebra
    saturatedChart A I (a : A) →ₐ[A] S := by
  let : Algebra A S := f.toAlgebra
  exact lift I a hreg hdiv

@[simp] theorem liftOfHom_algebraMap (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) (x : A) :
    liftOfHom I a f hreg hdiv (algebraMap A (saturatedChart A I (a : A)) x) = f x := by
  let : Algebra A S := f.toAlgebra
  exact (liftOfHom I a f hreg hdiv).commutes x

/-- The same actual algebra lift, as a ring map for affine scheme consumers. -/
def ringLift (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) :
    saturatedChart A I (a : A) →+* S := by
  let : Algebra A S := f.toAlgebra
  exact (liftOfHom I a f hreg hdiv).toRingHom

@[simp] theorem ringLift_algebraMap (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) (x : A) :
    ringLift I a f hreg hdiv (algebraMap A (saturatedChart A I (a : A)) x) = f x :=
  liftOfHom_algebraMap I a f hreg hdiv x

theorem ringLift_localizationTriangle (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) :
    (algebraMap S (Localization.Away (f (a : A)))).comp
        (ringLift I a f hreg hdiv) =
      (Localization.awayMap f (a : A)).comp
        (saturatedChart A I (a : A)).val.toRingHom := by
  let : Algebra A S := f.toAlgebra
  exact lift_localizationTriangle I a hreg hdiv

theorem liftOfHom_fraction_eq (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A))
    (b : I) (q : S) (hq : f (a : A) * q = f (b : A)) :
    liftOfHom I a f hreg hdiv (fractionElement I a b) = q := by
  let : Algebra A S := f.toAlgebra
  exact lift_fraction_eq I a hreg hdiv b q hq

/-- Base-compatible ring maps are unique under the original regularity condition. -/
theorem ringHom_ext (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (g h : saturatedChart A I (a : A) →+* S)
    (hg : g.comp (algebraMap A (saturatedChart A I (a : A))) = f)
    (hh : h.comp (algebraMap A (saturatedChart A I (a : A))) = f) : g = h := by
  let : Algebra A S := f.toAlgebra
  let gA : saturatedChart A I (a : A) →ₐ[A] S := {
    toRingHom := g
    commutes' := fun x => DFunLike.congr_fun hg x }
  let hA : saturatedChart A I (a : A) →ₐ[A] S := {
    toRingHom := h
    commutes' := fun x => DFunLike.congr_fun hh x }
  exact congrArg AlgHom.toRingHom (algHom_ext I a hreg gA hA)

/-- Existence and uniqueness for the literal saturated chart and actual base map.
The algebra-map version is `liftOfHom`, whose target algebra is exactly `f.toAlgebra`. -/
theorem existsUnique_ringHom (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) :
    ∃! g : saturatedChart A I (a : A) →+* S,
      g.comp (algebraMap A (saturatedChart A I (a : A))) = f := by
  refine ⟨ringLift I a f hreg hdiv, ?_, ?_⟩
  · ext x
    exact ringLift_algebraMap I a f hreg hdiv x
  · intro g hg
    apply ringHom_ext I a f hreg g (ringLift I a f hreg hdiv) hg
    ext x
    exact ringLift_algebraMap I a f hreg hdiv x

/-- Existence and uniqueness as an actual algebra map over exactly the supplied `f`. -/
theorem existsUnique_algHomOfHom (f : A →+* S) (hreg : IsRegular (f (a : A)))
    (hdiv : ∀ b : I, f (a : A) ∣ f (b : A)) :
    letI : Algebra A S := f.toAlgebra
    ∃! g : saturatedChart A I (a : A) →ₐ[A] S,
      ∀ b : I, f (a : A) * g (fractionElement I a b) = f (b : A) := by
  let : Algebra A S := f.toAlgebra
  exact existsUnique_algHom I a hreg hdiv

end RingHom
end Localization.Away.SaturatedChart
