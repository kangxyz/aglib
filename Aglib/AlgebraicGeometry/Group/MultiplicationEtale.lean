/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationFinite
public import Aglib.AlgebraicGeometry.Curves.Isogeny.Etale

/-!
# Etaleness of nonconstant multiplication in characteristic zero

The literal multiplication map of a smooth proper geometrically connected curve
group is finite, etale and surjective in characteristic zero provided it is
not the constant map to the actual origin. A point on any test scheme whose
`n`-th power is nontrivial supplies this condition.

The geometric derivation uses the proved nonconstant-to-dominant curve theorem,
proper-curve finiteness, and generic separability followed by translation and
descent. No etaleness theorem family is supplied as an assumption.

Target correspondence: finite and etale conjuncts of
`EllipticMultiplicationGeometry` in the frozen R5Lab packet, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
`AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean:283–286`.
The first-order proof in `Group.MultiplicationCotangent` supplies nonconstancy
for invertible scalars, and `Group.MultiplicationInvertible` proves the
finite-etale target in every characteristic. Degree `n * n` remains separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

/-- A nonconstant origin-preserving map between the actual curve groups is a
finite etale surjective group homomorphism in characteristic zero. -/
theorem pointed_nonconstant_finite_etale_of_charZero
    {k : Type u} [Field k] [CharZero k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G.X ⟶ H.X)
    (hp : η[G.X] ≫ f = η[H.X]) (hne : f ≠ 1) :
    IsMonHom f ∧ IsFinite f.left ∧ Etale f.left ∧ Surjective f.left := by
  let : IsMonHom f := pointedMorphism_of_curveProperties G H hG hH f hp
  obtain ⟨hf, hs⟩ := pointed_nonconstant_finite_surjective G H hG hH f hp hne
  let : IsFinite (Grp.ofHom f).hom.hom.left := by
    change IsFinite f.left
    exact hf
  let : Surjective (Grp.ofHom f).hom.hom.left := by
    change Surjective f.left
    exact hs
  exact ⟨inferInstance, hf, finite_hom_etale_of_charZero G H hG hH (Grp.ofHom f), hs⟩

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.Group.Multiplication

open AlgebraicGeometry.Scheme.OverField
attribute [local instance] Over.cartesianMonoidalCategory

/-- Nontrivial power on any actual test scheme detects nonconstancy of the
literal multiplication morphism. -/
theorem multiplication_ne_one_of_point
    {k : Type u} [Field k] (G : Grp (FScheme k)) (n : ℕ)
    {T : FScheme k} (x : T ⟶ G.X) (hx : x ^ n ≠ 1) : (𝟙 G.X) ^ n ≠ 1 := by
  intro h
  apply hx
  have he := congrArg (fun f : G.X ⟶ G.X => x ≫ f) h
  simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using he

/-- The actual nonconstant multiplication map is finite etale and surjective
over the original characteristic-zero field. -/
theorem multiplication_finite_etale_of_ne_one
    {k : Type u} [Field k] [CharZero k] (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hne : (𝟙 G.X) ^ n ≠ 1) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  (Curve.pointed_nonconstant_finite_etale_of_charZero G G hG hG _
    (multiplication_pointed G n) hne).2

/-- A single actual point not killed by `n` suffices for finite etale
multiplication in characteristic zero. The point may lie on any test scheme. -/
theorem multiplication_finite_etale_of_point
    {k : Type u} [Field k] [CharZero k] (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) {T : FScheme k}
    (x : T ⟶ G.X) (hx : x ^ n ≠ 1) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  multiplication_finite_etale_of_ne_one G hG n (multiplication_ne_one_of_point G n x hx)

/-- The same result uses the native prescribed-origin group-law data without
changing its group object, multiplication morphism, or origin. -/
theorem pointedGroupLaw_multiplication_finite_etale_of_ne_one
    {k : Type u} [Field k] [CharZero k] {C : FScheme k}
    {c : 𝟙_ (FScheme k) ⟶ C} (L : PointedGroupLaw C c) (hC : Curve.Properties C)
    (n : ℕ) (hne : letI : GrpObj C := L.law; (𝟙 C) ^ n ≠ 1) :
    letI : GrpObj C := L.law
    IsFinite ((𝟙 C) ^ n).left ∧ Etale ((𝟙 C) ^ n).left ∧
      Surjective ((𝟙 C) ^ n).left := by
  let : GrpObj C := L.law
  exact multiplication_finite_etale_of_ne_one { X := C, grp := L.law } hC n hne

/-- Multiplication by one is finite etale and surjective in every
characteristic, with no geometric hypotheses on the group scheme. -/
theorem multiplication_one_finite_etale
    {k : Type u} [Field k] (G : Grp (FScheme k)) :
    IsFinite ((𝟙 G.X) ^ (1 : ℕ)).left ∧ Etale ((𝟙 G.X) ^ (1 : ℕ)).left ∧
      Surjective ((𝟙 G.X) ^ (1 : ℕ)).left := by
  simp only [pow_one, Over.id_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Group.Multiplication
