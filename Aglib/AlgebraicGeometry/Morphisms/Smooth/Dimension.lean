/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity

/-!
Exact maximal/closed stalk dimension and global dimension for smooth schemes
over arbitrary fields, including n=0 and non-quasi-compact schemes. The point
chosen for the global lower bound is only maximal in its affine chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- A maximal point in an etale polynomial chart has dimension n. -/
theorem etale_polynomial_stalk_dimension_of_isMaximal
    (K : Type u) [Field K] (n : ℕ) {B : Type u} [CommRing B]
    (g : MvPolynomial (Fin n) K →+* B) (hg : g.Etale) (q : Spec (.of B))
    [q.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (.of B)).presheaf.stalk q) = n := by
  let φ := Spec.map (CommRingCat.ofHom g)
  let : Etale φ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  let : IsRegularLocalRing
      ((Spec (.of (MvPolynomial (Fin n) K))).presheaf.stalk (φ q)) :=
    polynomial_spec_stalk_isRegularLocalRing K n (φ q)
  let : (φ q).asIdeal.IsMaximal := isMaximal_comap_etale_polynomial K n g hg q.asIdeal
  rw [AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_of_etale φ q]
  exact polynomial_spec_stalk_dimension_of_isMaximal K n (φ q)

/-- Exact term of the original closed-point dimension interface. The residue
field may be inseparable over the base field. -/
theorem smoothClosedPointDimension : SmoothClosedPointDimension.{u} := by
  intro K _ X f n hf x hclosed
  let : SmoothOfRelativeDimension n f := hf
  obtain ⟨V, hV, hx, g, hg⟩ :=
    exists_etale_polynomial_chart_of_smoothOfRelativeDimension K X f n x
  let q := hV.isoSpec.hom ⟨x, hx⟩
  have hxq : hV.fromSpec q = x := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hx⟩ = x
    rw [hV.isoSpec_hom_fromSpec]
    rfl
  have hpre : hV.fromSpec ⁻¹' ({x} : Set X) = {q} := by
    ext z
    change (hV.fromSpec z = x) ↔ z = q
    rw [← hxq, hV.fromSpec.isOpenEmbedding.injective.eq_iff]
  have hqclosed : IsClosed ({q} : Set (Spec Γ(X, V))) := by
    rw [← hpre]
    exact hclosed.preimage hV.fromSpec.continuous
  let : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqclosed
  have hd := etale_polynomial_stalk_dimension_of_isMaximal K n g hg q
  rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
  rwa [← coheight_eq_of_isOpenImmersion hV.fromSpec, hxq] at hd

/-- Exact term of the original nonempty smooth-field dimension interface.
The lower-bound point lies in a nonempty affine chart and need not be closed
in the whole scheme. -/
theorem smoothFieldDimension : SmoothFieldDimension.{u} := by
  intro K _ X f n hf hnonempty
  let : SmoothOfRelativeDimension n f := hf
  let : Nonempty X := hnonempty
  have hupper : topologicalKrullDim X ≤ n := by
    rw [topologicalKrullDim_eq_iSup_stalk]
    exact iSup_le (smoothOfRelativeDimension_stalk_dimension_le K X f n)
  obtain ⟨x⟩ := hnonempty
  obtain ⟨V, hV, hx, g, hg⟩ :=
    exists_etale_polynomial_chart_of_smoothOfRelativeDimension K X f n x
  let qx := hV.isoSpec.hom ⟨x, hx⟩
  obtain ⟨m, hm, _⟩ := qx.asIdeal.exists_le_maximal qx.2.ne_top
  let q : Spec Γ(X, V) := ⟨m, hm.isPrime⟩
  let : q.asIdeal.IsMaximal := hm
  have hd := etale_polynomial_stalk_dimension_of_isMaximal K n g hg q
  have hdX : ringKrullDim (X.presheaf.stalk (hV.fromSpec q)) = n := by
    rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion hV.fromSpec,
      ← ringKrullDim_stalk_eq_coheight]
    exact hd
  have hlower : n ≤ topologicalKrullDim X := by
    rw [← hdX, topologicalKrullDim_eq_iSup_stalk]
    exact le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) (hV.fromSpec q)
  exact le_antisymm hupper hlower

end AlgebraicGeometry.Scheme
