/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Length.PrincipalIntersection
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.FiniteSupportLengths

/-!
# Singular local-order components of the proper-curve product formula

The local order is `Scheme.ord` on the actual function field, with its actual
stalk fraction-field map. These lemmas identify its sign and residue-weighted
value with principal quotient dimensions. No smoothness, normality, or DVR
hypothesis is introduced.

The intended full target remains `ProperCurveProductFormula` in
`Picard/Degree.lean:117`: proper integral Noetherian field schemes of dimension
exactly one, including singular curves. The global finite-support sheaf Euler
comparison and proper coherent finiteness are not asserted by these local
components. Input basis is the unchanged source at
`f1a725686388bcc5d2eb9c9ec0971d7400cf4c7a`, through disjoint handoff commit
`914476dd55baa6feaef45710e946922ea011eb0c`, with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.ProductFormula

open FiniteSupportLengths



universe u
variable (X : Scheme.{u}) [IsIntegral X]

attribute [local instance] specializationOrder in
/-- On an integral dimension-one scheme, every closed point is codimension one.
No smoothness or regularity theorem is used. -/
theorem closedPoint_coheight_one (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : IsClosed ({x} : Set X)) : Order.coheight x = 1 := by
  have hd : Order.krullDim X = 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hu : Order.coheight x ≤ 1 := by
    exact_mod_cast (Order.coheight_le_krullDim x).trans_eq hd
  have hn : Order.coheight x ≠ 0 := by
    rw [Order.coheight_ne_zero]
    intro hmax
    have he : x = genericPoint X :=
      le_antisymm (genericPoint_specializes x) (hmax (genericPoint_specializes x))
    have hg : IsClosed ({genericPoint X} : Set X) := he ▸ hx
    have hs : ({genericPoint X} : Set X) = Set.univ :=
      hg.closure_eq.symm.trans (genericPoint_spec X).def
    let : Subsingleton X := ⟨fun y z => by
      have hy : y = genericPoint X := Set.mem_singleton_iff.mp (hs.symm ▸ Set.mem_univ y)
      have hz : z = genericPoint X := Set.mem_singleton_iff.mp (hs.symm ▸ Set.mem_univ z)
      exact hy.trans hz.symm⟩
    have hf := Order.krullDim_nonpos_of_subsingleton (α := X)
    rw [hd] at hf
    norm_num at hf
  exact le_antisymm hu (Order.one_le_iff_ne_zero.mpr hn)

variable [IsNoetherian X]

/-- The actual order of a nonzero stalk element is its finite principal colength,
including at singular codimension-one points. -/
theorem order_stalk_element (x : X) (hx : Order.coheight x = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x =
      (stalkColength X x a : ℤ) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hn : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne ha
  rw [Scheme.ord_eq_iff hx hn]
  change Ring.ordFrac (X.presheaf.stalk x) _ = _
  rw [Ring.ordFrac_eq_ord (X.presheaf.stalk x) ha]
  apply Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk x)
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  exact (ENat.natCast_toNat
    (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr ha))).symm

/-- Numerators contribute positively and denominators negatively to the actual
singular local order. Both colengths are computed in the same actual stalk. -/
theorem order_stalk_fraction (x : X) (hx : Order.coheight x = 1)
    (a b : X.presheaf.stalk x) (ha : a ≠ 0) (hb : b ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b) x =
      (stalkColength X x a : ℤ) - (stalkColength X x b : ℤ) := by
  have haK : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne ha
  have hbK : algebraMap (X.presheaf.stalk x) X.functionField b ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne hb
  have h := Scheme.ord_mul (x := x) (div_ne_zero haK hbK) hbK
  rw [div_mul_cancel₀ _ hbK, order_stalk_element X x hx a ha,
    order_stalk_element X x hx b hb] at h
  omega

/-- The same actual singular order through the finite images of the two
principal ideals in their common-intersection quotient. -/
theorem order_stalk_fraction_eq_intersection_image_lengths
    (x : X) (hx : Order.coheight x = 1) (a b : X.presheaf.stalk x)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b) x =
      ((Module.length (X.presheaf.stalk x)
        (Ideal.quotientIdealImage (X.presheaf.stalk x) (Ideal.span {a} ⊓ Ideal.span {b})
          (Ideal.span {b}))).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk x)
          (Ideal.quotientIdealImage (X.presheaf.stalk x) (Ideal.span {a} ⊓ Ideal.span {b})
            (Ideal.span {a}))).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact (order_stalk_fraction X x hx a b ha hb).trans
    (Ideal.principalIntersection_image_length_difference (X.presheaf.stalk x) a b ha hb).symm

omit [AlgebraicGeometry.IsNoetherian X] in
/-- A nonzero function has nonzero numerator and denominator in every actual
stalk, using that stalk's existing fraction-field embedding. -/
theorem exists_stalk_fraction (x : X) (f : X.functionFieldˣ) :
    ∃ a b : X.presheaf.stalk x, a ≠ 0 ∧ b ≠ 0 ∧
      algebraMap (X.presheaf.stalk x) X.functionField a /
        algebraMap (X.presheaf.stalk x) X.functionField b = (f : X.functionField) := by
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective (X.presheaf.stalk x)
    (f : X.functionField)
  have ha : a ≠ 0 := by
    intro ha
    apply f.ne_zero
    rw [← he, ha, map_zero, zero_div]
  exact ⟨a, b, ha, mem_nonZeroDivisors_iff_ne_zero.mp hb, he⟩

variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType p] in
/-- Dimension of the actual principal stalk quotient on the structural base scalars. -/
def stalkQuotientDimension (x : X) (a : X.presheaf.stalk x) : ℕ :=
  letI := stalkConstantsAlgebra X p x
  Module.finrank k (X.presheaf.stalk x ⧸ Ideal.span {a})

/-- The existing residue weight converts the actual fraction order into the
signed difference of actual base-field principal-quotient dimensions. -/
theorem weighted_order_stalk_fraction (x : X) (hx : IsClosed ({x} : Set X))
    (hcodim : Order.coheight x = 1) (a b : X.presheaf.stalk x)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    letI := stalkConstantsAlgebra X p x
    Degree.weight X p ⟨x, hx⟩ *
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField a /
        algebraMap (X.presheaf.stalk x) X.functionField b) x =
      (Module.finrank k (X.presheaf.stalk x ⧸ Ideal.span {a}) : ℤ) -
        (Module.finrank k (X.presheaf.stalk x ⧸ Ideal.span {b}) : ℤ) := by
  let := stalkConstantsAlgebra X p x
  rw [order_stalk_fraction X x hcodim a b ha hb,
    stalkQuotient_finrank_eq_weight_mul_colength X p x hx hcodim a ha,
    stalkQuotient_finrank_eq_weight_mul_colength X p x hx hcodim b hb]
  ring

/-- An actual principal degree on a singular dimension-one field scheme is a
finite sum of signed actual stalk-quotient dimensions. Nonzero stalk fractions
are constructed for the given function, not assumed as extra data. The global
Euler comparison needed to show this sum vanishes remains separate. -/
theorem principal_degree_quotient_formula (hdim : topologicalKrullDim X = 1)
    (f : X.functionFieldˣ) :
    ∃ a b : (x : Scheme.ClosedPoint X) → X.presheaf.stalk x.val,
      (∀ x, a x ≠ 0 ∧ b x ≠ 0 ∧
        algebraMap (X.presheaf.stalk x.val) X.functionField (a x) /
          algebraMap (X.presheaf.stalk x.val) X.functionField (b x) = (f : X.functionField)) ∧
      Degree.degDiv X p (Divisors.principal X (Additive.ofMul f)) =
        ∑ x ∈ (Divisors.principal X (Additive.ofMul f)).support,
          ((stalkQuotientDimension X p x.val (a x) : ℤ) -
            (stalkQuotientDimension X p x.val (b x) : ℤ)) := by
  classical
  choose a b ha hb he using fun x : Scheme.ClosedPoint X => exists_stalk_fraction X x.val f
  refine ⟨a, b, fun x => ⟨ha x, hb x, he x⟩, ?_⟩
  rw [Degree.degDiv_apply]
  apply Finset.sum_congr rfl
  intro x _
  have h := weighted_order_stalk_fraction X p x.val x.property
    (closedPoint_coheight_one X hdim x.val x.property) (a x) (b x) (ha x) (hb x)
  rw [he x] at h
  change X.ord (f : X.functionField) x.val * Degree.weight X p x = _
  rw [mul_comm]
  exact h

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.ProductFormula
