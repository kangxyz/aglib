/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Charts
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Stalk.EtalePolynomial

/-!
Universal smooth-field regularity and dimension suppliers. The actual etale
polynomial coordinates come from pinned standard-smooth presentations, and the
local-etale bridge is applied to the actual scheme stalk map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u


/-- Exact term of the original all-fields, all-smooth-schemes regularity
interface, without perfectness, characteristic or relative-dimension premises. -/
theorem smoothFieldRegularity : SmoothFieldRegularity.{u} := by
  intro K _ X f hf x
  let : Smooth f := hf
  obtain ⟨V, hV, hx, n, g, hg⟩ := exists_etale_polynomial_chart_of_smooth K X f x
  let q := hV.isoSpec.hom ⟨x, hx⟩
  have hxq : hV.fromSpec q = x := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hx⟩ = x
    rw [hV.isoSpec_hom_fromSpec]
    rfl
  let : IsRegularLocalRing ((Spec Γ(X, V)).presheaf.stalk q) :=
    etale_polynomial_stalk_isRegularLocalRing K n g hg q
  let e := (asIso (hV.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv
  have hr : IsRegularLocalRing (X.presheaf.stalk (hV.fromSpec q)) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  exact hxq ▸ hr

/-- Every actual stalk of a smooth scheme of relative dimension n over any
field has dimension at most n. Generic points are included. -/
theorem smoothOfRelativeDimension_stalk_dimension_le
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨V, hV, hx, g, hg⟩ :=
    exists_etale_polynomial_chart_of_smoothOfRelativeDimension K X f n x
  let q := hV.isoSpec.hom ⟨x, hx⟩
  have hxq : hV.fromSpec q = x := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hx⟩ = x
    rw [hV.isoSpec_hom_fromSpec]
    rfl
  have hd := etale_polynomial_stalk_dimension_le K n g hg q
  rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
  rwa [← coheight_eq_of_isOpenImmersion hV.fromSpec, hxq] at hd

end AlgebraicGeometry.Scheme
