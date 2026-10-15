/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Charts
public import Aglib.AlgebraicGeometry.Stalk.Polynomial
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap

/-!
Universal smooth-field regularity and dimension suppliers. The actual etale
polynomial coordinates come from pinned standard-smooth presentations, and the
local-etale bridge is applied to the actual scheme stalk map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- An actual affine etale polynomial chart has regular local rings. -/
theorem etale_polynomial_stalk_isRegularLocalRing
    (K : Type u) [Field K] (n : ℕ) {B : Type u} [CommRing B]
    (g : MvPolynomial (Fin n) K →+* B) (hg : g.Etale) (q : Spec (.of B)) :
    IsRegularLocalRing ((Spec (.of B)).presheaf.stalk q) := by
  let φ := Spec.map (CommRingCat.ofHom g)
  let : Etale φ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  let : IsRegularLocalRing
      ((Spec (.of (MvPolynomial (Fin n) K))).presheaf.stalk (φ q)) :=
    polynomial_spec_stalk_isRegularLocalRing K n (φ q)
  exact AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_of_etale φ q

/-- Dimension in an actual affine etale polynomial chart is at most its
number of coordinates at every point. -/
theorem etale_polynomial_stalk_dimension_le
    (K : Type u) [Field K] (n : ℕ) {B : Type u} [CommRing B]
    (g : MvPolynomial (Fin n) K →+* B) (hg : g.Etale) (q : Spec (.of B)) :
    ringKrullDim ((Spec (.of B)).presheaf.stalk q) ≤ n := by
  let φ := Spec.map (CommRingCat.ofHom g)
  let : Etale φ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  let : IsRegularLocalRing
      ((Spec (.of (MvPolynomial (Fin n) K))).presheaf.stalk (φ q)) :=
    polynomial_spec_stalk_isRegularLocalRing K n (φ q)
  rw [AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_of_etale φ q]
  exact polynomial_spec_stalk_dimension_le K n (φ q)

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
