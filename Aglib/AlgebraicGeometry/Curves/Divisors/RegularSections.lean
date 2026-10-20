/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/



/-!
# Regular sections from the actual stalks

C2 foundation, K2-018 `lem:k2018-geometric-exact-order`, source basis `7f86e4a`.
Arbitrary-open extension is proved by actual sheaf gluing. Nonnegative local
orders are equivalent to membership in actual DVR stalks. These are proved
local-to-global statements, with no retained theorem premise.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.OverField.Curve.Divisors
universe u
variable (X : Scheme.{u}) [IsIntegral X]

theorem exists_section_of_mem_stalk (U : X.Opens) [hU : Nonempty U] (f : X.functionField)
    (hf : ∀ x : U, ∃ r : X.presheaf.stalk x.val,
      algebraMap (X.presheaf.stalk x.val) X.functionField r = f) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  choose r hr using hf
  choose V hx s hs using fun x => X.presheaf.exists_germ_eq (r x)
  let W (x : U) := V x ⊓ U
  let t (x : U) : Γ(X, W x) := X.presheaf.map ((V x).infLELeft U).op (s x)
  let (x : U) : Nonempty (W x) := ⟨⟨x.val, hx x, x.property⟩⟩
  have he (x : U) : X.germToFunctionField (W x) (t x) = f := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X
      (show x.val ∈ W x from ⟨hx x, x.property⟩)]
    change algebraMap (X.presheaf.stalk x.val) X.functionField
      (X.presheaf.germ (W x) x.val _ (X.presheaf.map ((V x).infLELeft U).op (s x))) = f
    rw [X.presheaf.germ_res_apply, hs, hr]
  let (x : U) : Nonempty (V x) := ⟨⟨x.val, hx x⟩⟩
  have heV (x : U) : X.germToFunctionField (V x) (s x) = f := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (hx x), hs, hr]
  have hc : TopCat.Presheaf.IsCompatible X.presheaf W t := by
    intro x y
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    change X.presheaf.germ (W x ⊓ W y) z hz
      (X.presheaf.map ((W x).infLELeft (W y)).op (t x)) =
      X.presheaf.germ (W x ⊓ W y) z hz
      (X.presheaf.map ((W x).infLERight (W y)).op (t y))
    apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
    simp only [t, W, X.presheaf.germ_res_apply]
    rw [Scheme.algebraMap_germ_eq_germToFunctionField X hz.1.1,
      Scheme.algebraMap_germ_eq_germToFunctionField X hz.2.1, heV, heV]
  have hcover : U ≤ iSup W := by
    intro x hxU
    exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx _, hxU⟩
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' W U
    (fun _ => homOfLE inf_le_right) hcover t hc
  refine ⟨g, ?_⟩
  let x := hU.some
  have h := he x
  rw [← hg] at h
  change X.presheaf.germ (W x) (genericPoint X) _
    (X.presheaf.map (homOfLE inf_le_right).op g) = f at h
  rw [X.presheaf.germ_res_apply] at h
  exact h

variable [IsNoetherian X]

theorem order_nonneg_iff_mem_stalk (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f : X.functionField) :
    0 ≤ X.ord f x ↔ ∃ r : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField r = f := by
  by_cases hf : f = 0
  · simp [hf]
  have hx := AlgebraicGeometry.Scheme.OverField.Curve.Divisors.coheight_eq_one_of_dvr X x
  rw [Scheme.le_ord_iff hx hf]
  change 1 ≤ Ring.ordFrac (X.presheaf.stalk x) f ↔ _
  rw [Ring.ordFrac_eq_valuation_inv]
  have hv : (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation X.functionField
    f ≠ 0 :=
    (map_ne_zero _).mpr hf
  rw [one_le_inv₀ (zero_lt_iff.mpr hv)]
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨r, rfl⟩
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r

open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

theorem exists_section_of_nonneg_orders (hdim : topologicalKrullDim X ≤ 1)
    (U : X.Opens) [Nonempty U] (f : X.functionField)
    (hf : ∀ x : ClosedPoint X, x.val ∈ U → 0 ≤ X.ord f x.val) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  apply exists_section_of_mem_stalk X U f
  intro x
  rcases point_eq_generic_or_isClosed X hdim x.val with hg | hx
  · rw [hg]
    refine ⟨f, ?_⟩
    simp [RingHom.algebraMap_toAlgebra]
  · let y : ClosedPoint X := ⟨x.val, hx⟩
    let : IsDiscreteValuationRing (X.presheaf.stalk x.val) :=
      inferInstanceAs (IsDiscreteValuationRing (X.presheaf.stalk y.val))
    exact (order_nonneg_iff_mem_stalk X x.val f).mp (hf y x.property)


end AlgebraicGeometry.Scheme.OverField.Curve.Divisors
