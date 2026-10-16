/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.Polynomial
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.RingTheory.Etale.Polynomial

/-!
# Stalks in etale polynomial charts

An actual etale map from a finite polynomial algebra over an arbitrary field
has regular source stalks and the stated dimension bound. Equality of dimension
is asserted only at maximal points. No smooth scheme map, perfect field or
separability premise is added.

Source at 451aeda6b8bb5b44402b574dd6cf60f912360f8c:
Aglib/AlgebraicGeometry/Morphisms/Smooth/Regularity.lean:26–50 and
Aglib/AlgebraicGeometry/Morphisms/Smooth/Dimension.lean:24–37.
The sole proof-token adaptation is the approved native ring-lemma name.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

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
  let : (φ q).asIdeal.IsMaximal := RingHom.Etale.isMaximal_comap_polynomial K n g hg q.asIdeal
  rw [AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_of_etale φ q]
  exact polynomial_spec_stalk_dimension_of_isMaximal K n (φ q)

end AlgebraicGeometry.Scheme
