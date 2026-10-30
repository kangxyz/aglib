/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.AffineMap
public import Aglib.AlgebraicGeometry.Picard.IdentityComponent
public import Aglib.AlgebraicGeometry.Picard.Scheme.Properties
public import Aglib.AlgebraicGeometry.Picard.Smooth.Lifting
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Smoothness of the Picard scheme of a curve

Let `k` be a field and `X ⊆ P^N_k` closed, flat with geometrically integral fibres
(`p = i ≫ toSpec k ι`), and let `P = picardScheme h` be its Picard scheme. Suppose that `X` is
integral of dimension one. Then `P` and its identity component `Pic⁰_{X/k}` are smooth over `k`
(`smooth_picardScheme_of_curve`).

Source: Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Prop. 5.19, p. 47, for curves.

* With a section `o` of `p`, `P` represents the relative functor `T ↦ Pic(X_T) / Pic(T)` on
  locally Noetherian test schemes (Kleiman, Thm 2.5(2), p. 18;
  `picardSchemeRelativeRepresentableByOfIsSplitEpi`). The finite map `X ⟶ P^1_k` of
  `exists_finite_dominant_map_to_nativeP1` is affine (`exists_isAffineHom_to_projectiveP1`), so
  `liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1` lifts
  the points of `P` (`liftsAlongNoetherianSquareZero_picardScheme_of_curve_of_section`), and `P`
  is smooth (`smooth_picardScheme_of_curve_of_section`).
* In general, let `K` be the residue field of a point `x` of `X`. Then `X_K = X ×_k K` has the
  section given by `x`, `P_K = P ×_k K` represents `Pic_{X_K/K,(fppf)}`
  (`baseChangeRepresentableBy`, Kleiman, Ex. 4.4, p. 27), hence the relative functor of `X_K`
  (Kleiman, Thm 2.5(2)), and `X_K ⟶ X ⟶ P^1_k` is affine. So `P_K` is smooth over `K`, and
  smoothness descends along the faithfully flat quasi-compact `Spec K ⟶ Spec k` (Mathlib's
  `MorphismProperty.of_pullback_snd_of_descendsAlong` with the descent of `Smooth` in
  `AlgebraicGeometry/Morphisms/LocalFlatDescent.lean`). Kleiman reduces instead to an
  algebraically closed residue field by a flat local base change.

The identity component is an open subscheme (`isOpenImmersion_picardIdentityComponentι`), hence
smooth with `P`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

-- Base change of `IsProper` is synthesized with relaxed type transparency, as in Mathlib's
-- `AlgebraicGeometry/Geometrically/Integral.lean` for geometric integrality.
set_option backward.isDefEq.respectTransparency.types false in
/-- The base change `X_A ⟶ Spec A` of a proper `X ⟶ Spec k` is proper. -/
theorem isProper_pullback_snd_specOver {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (A : Type u) [CommRing A] [Algebra k A] :
    IsProper (pullback.snd p (specOver k A).hom) :=
  MorphismProperty.pullback_snd _ _ inferInstance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.RelativePicard

open Strata

variable {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace k ι} [IsClosedImmersion i] [Flat (i ≫ toSpec k ι)]
  [GeometricallyIntegral (i ≫ toSpec k ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- **Points of the Picard scheme of a curve with a rational point lift along square-zero
thickenings** (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Prop. 5.19, p. 47,
for curves). Let `X ⊆ P^N_k` be closed, flat with geometrically integral fibres, integral of
dimension one, with a section `o` of `p = i ≫ toSpec k ι`. For every surjection `g : A' → A` of
`k`-algebras with `A'` Noetherian and square-zero kernel, every `A`-point of `picardScheme h`
over `k` lifts to an `A'`-point. -/
theorem liftsAlongNoetherianSquareZero_picardScheme_of_curve_of_section (o : Spec (.of k) ⟶ X)
    (ho : o ≫ i ≫ toSpec k ι = 𝟙 _) [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    (picardScheme h).obj.hom.LiftsAlongNoetherianSquareZero := by
  have : IsSplitEpi (i ≫ toSpec k ι) := IsSplitEpi.mk' ⟨o, ho⟩
  have := isProper_comp_toSpec_of_isClosedImmersion i e
  obtain ⟨ρ, hρ⟩ :=
    OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1 (i ≫ toSpec k ι) hdim
  exact liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1 _
    (picardSchemeRelativeRepresentableByOfIsSplitEpi h) ρ

/-- The identity component of `picardScheme h` is smooth over `k` when `picardScheme h` is. -/
theorem smooth_picardIdentityComponent_of_smooth (hs : Smooth (picardScheme h).obj.hom) :
    Smooth (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
      (picardSchemeRepresentableBy h)).hom := by
  rw [← Over.w (picardIdentityComponentι (i ≫ toSpec k ι) (picardScheme h)
    (picardSchemeRepresentableBy h))]
  infer_instance

/-- **Smoothness of the Picard scheme of a curve with a rational point** (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Prop. 5.19, p. 47, for curves). Let `k` be a field and `X ⊆ P^N_k`
closed, flat with geometrically integral fibres, integral of dimension one, with a section `o` of
`p = i ≫ toSpec k ι`. Then `picardScheme h` is smooth over `k`, and so is its identity component
`Pic⁰_{X/k}`, an open subscheme. -/
theorem smooth_picardScheme_of_curve_of_section (o : Spec (.of k) ⟶ X)
    (ho : o ≫ i ≫ toSpec k ι = 𝟙 _) [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    Smooth (picardScheme h).obj.hom ∧
      Smooth (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom := by
  have hs : Smooth (picardScheme h).obj.hom :=
    Scheme.Hom.smooth_of_liftsAlongNoetherianSquareZero
      (liftsAlongNoetherianSquareZero_picardScheme_of_curve_of_section h o ho hdim)
  exact ⟨hs, smooth_picardIdentityComponent_of_smooth h hs⟩

/-- **Smoothness of the Picard scheme of a curve** (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Prop. 5.19, p. 47, for curves). Let `k` be a field and `X ⊆ P^N_k` closed,
flat with geometrically integral fibres and integral of dimension one; no rational point is
assumed. Then `picardScheme h` is smooth over `k`, and so is its identity component `Pic⁰_{X/k}`.
The proof base changes to the residue field `K` of a point of `X`, where `X_K` has a section, and
descends smoothness along `Spec K ⟶ Spec k`. -/
theorem smooth_picardScheme_of_curve [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    Smooth (picardScheme h).obj.hom ∧
      Smooth (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom := by
  have : IsProper (i ≫ toSpec k ι) := isProper_comp_toSpec_of_isClosedImmersion i e
  obtain ⟨x⟩ : Nonempty X := inferInstance
  let : Algebra k (X.residueField x) :=
    ((X.residue x).hom.comp ((i ≫ toSpec k ι).stalkScalar x)).toAlgebra
  -- The point `x` is a `K`-point of `X` over `k`, `K = κ(x)`.
  have hy : X.fromSpecResidueField x ≫ i ≫ toSpec k ι =
      (specOver k (X.residueField x)).hom := by
    rw [Scheme.fromSpecResidueField, Category.assoc, fromSpecStalk_comp_eq_spec_map_stalkScalar,
      ← Spec.map_comp]
    rfl
  -- The base change `X_K ⟶ Spec K` has a section.
  have : IsSplitEpi (pullback.snd (i ≫ toSpec k ι) (specOver k (X.residueField x)).hom) :=
    IsSplitEpi.mk' ⟨pullback.lift (X.fromSpecResidueField x) (𝟙 _) (by rw [hy, Category.id_comp]),
      pullback.lift_snd _ _ _⟩
  have := isProper_pullback_snd_specOver (i ≫ toSpec k ι) (X.residueField x)
  have : IsLocallyNoetherian (specOver k (X.residueField x)).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (X.residueField x))))
  -- `P_K` represents the relative Picard functor of `X_K`, and `X_K ⟶ P^1_k` is affine.
  let RK := relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral _
    (baseChangeRepresentableBy (i ≫ toSpec k ι) (specOver k (X.residueField x)).hom
      (picardScheme h) (picardSchemeRepresentableBy h))
  obtain ⟨ρ, hρ⟩ :=
    OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1 (i ≫ toSpec k ι) hdim
  have := isAffineHom_pullback_fst_specOver (i ≫ toSpec k ι) (X.residueField x)
  have hK :=
    liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1 _ RK
      (pullback.fst (i ≫ toSpec k ι) (specOver k (X.residueField x)).hom ≫ ρ)
  have : LocallyOfFiniteType (LocallyNoetherianOver.baseChange
      (specOver k (X.residueField x)).hom (picardScheme h)).obj.hom :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (picardScheme h).obj.hom (specOver k (X.residueField x)).hom))
  have hsK := Scheme.Hom.smooth_of_liftsAlongNoetherianSquareZero hK
  -- Descent along the faithfully flat quasi-compact `Spec K ⟶ Spec k`.
  have : Nonempty (specOver k (X.residueField x)).left :=
    inferInstanceAs (Nonempty (Spec (.of (X.residueField x))))
  have : Surjective (specOver k (X.residueField x)).hom :=
    ⟨Function.surjective_to_subsingleton _⟩
  have : Flat (specOver k (X.residueField x)).hom :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : QuasiCompact (specOver k (X.residueField x)).hom :=
    (inferInstance : QuasiCompact (Spec.algebraMap k (X.residueField x)))
  have hs : Smooth (picardScheme h).obj.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := (picardScheme h).obj.hom)
      (g := (specOver k (X.residueField x)).hom) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      hsK
  exact ⟨hs, smooth_picardIdentityComponent_of_smooth h hs⟩

end AlgebraicGeometry.Scheme.RelativePicard
