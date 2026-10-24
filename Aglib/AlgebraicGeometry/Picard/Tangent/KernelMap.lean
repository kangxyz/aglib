/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Comparison

/-!
# Kleiman's map `v : H^1(X, 𝒪_X) → T_0 Pic_{X/k}`

Let `k` be a field, `X : FScheme k` with `X.left` separated and structure map `p`, `U` a cover of
`X` by affine opens, and `F = Pic_{X/k,(fppf)}` (`(fppfPicardSheaf p).obj`). Let
`ρ : Spec k ⟶ Spec k[ε]` be the closed point (`DualNumbers.closedPointOver k`) and
`µ_a : ε ↦ a ε` the scaling (`DualNumbers.scaleOver k a`).

`DualNumbers.cohomologyToFppfPicardKer X U hU hU₁ : H^1(X, 𝒪_X) →+ ker F(ρ)` is Kleiman's `v`
(*The Picard scheme*, arXiv:math/0504020v1, proof of Thm 5.11, p. 43): the inverse of the Čech
comparison `DualNumbers.picardKerEquivCech : ker(Pic X[ε] → Pic X) ≃+ H^1(X, 𝒪_X)`, followed by
the map of the horizontal kernels of Square (5.11.4), `DualNumbers.picardKerToFppf X`, whose
underlying map is `Pic(X[ε]) → P_{X/k}(k[ε]) → F(k[ε])` (`quotientProjection`, then
`toFppfPicardSheaf`). It lands in `ker F(ρ)` because the square commutes by naturality of the
sheafification unit. No section of `p` is used.

* `v` is additive by construction, and it is linear for the scalars `a • t = F(µ_a) t` on the
  target (Kleiman, p. 42, after (5.11.1)): `v (a • c) = F(µ_a) (v c)`
  (`cohomologyToFppfPicardKer_smul`), from `picardKerEquivCech_dualScale` and naturality of the unit
  along `µ_a`.
* For `p` proper and flat with geometrically integral fibres, `v` is injective
  (`cohomologyToFppfPicardKer_injective_of_isProper_of_flat_of_geometricallyIntegral`; Kleiman,
  Thm 2.5(1), p. 18, and `Pic(k[ε]) = 0`).
* If moreover `p` has a section, `v` is the inverse of the equivalence
  `fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X` (Kleiman, Thm 2.5(2),
  p. 18) applied after the inverse Čech comparison
  (`cohomologyToFppfPicardKer_eq_symm_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`),
  hence bijective:
  `cohomologyToFppfPicardKer_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`.

The scaling `DualNumbers.scaleRingHom k a` is Mathlib's `TrivSqZeroExt.map (a • LinearMap.id)`
(`scaleRingHom_eq_map`, `scaleRingHom_eq_restrictScalars_map`), for any commutative ring `k`.

Kleiman obtains `v` from the square of `H^1(𝒪^*)` and the étale sheaf; here the top row is
`Pic(X[ε]) → Pic(X)`, computed by Čech cocycles on `U`, and the vertical maps are the fppf
sheafification unit.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.DualNumbers

section Ring

variable (k : Type u) [CommRing k]

/-- The scaling `µ_a : x + y ε ↦ x + a y ε` is Mathlib's `TrivSqZeroExt.map` of multiplication by
`a` on `k[ε] = TrivSqZeroExt k k`. -/
theorem scaleRingHom_eq_map (a : k) :
    scaleRingHom k a = (TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k)).toRingHom := by
  apply DualNumber.ringHom_ext
  · refine RingHom.ext fun r => ?_
    change scaleRingHom k a (TrivSqZeroExt.inl r) =
      TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k) (TrivSqZeroExt.inl r)
    rw [scaleRingHom_inl, TrivSqZeroExt.map_inl]
  · change scaleRingHom k a DualNumber.eps =
      TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k) (TrivSqZeroExt.inr 1)
    rw [scaleRingHom_eps, TrivSqZeroExt.map_inr, LinearMap.smul_apply, LinearMap.id_apply,
      DualNumber.eps, TrivSqZeroExt.inl_mul_inr]

/-- `scaleRingHom_eq_map` with the `k`-algebra map restricted to `k`, as for the scalars of a
`k`-point over a field extension `L/k` at `L = k`. -/
theorem scaleRingHom_eq_restrictScalars_map (a : k) :
    scaleRingHom k a =
      ((TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k)).restrictScalars k).toRingHom :=
  scaleRingHom_eq_map k a

end Ring

section Field

variable {k : Type u} [Field k] (X : FScheme k) [X.left.IsSeparated] {ι : Type u}
  (U : ι → X.left.Opens) (hU : iSup U = ⊤) (hU₁ : ∀ j, IsAffineOpen (U j))

/-- **Kleiman's map `v : H^1(X, 𝒪_X) → T_0 Pic_{X/k}`** (arXiv:math/0504020v1, proof of Thm 5.11,
p. 43): the inverse of the Čech comparison `picardKerEquivCech` on the cover `U`, followed by the
map `ker(i^*) → ker F(ρ)` of the horizontal kernels of Square (5.11.4). -/
def cohomologyToFppfPicardKer :
    structureCohomology k X 1 →+
      ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker :=
  (picardKerToFppf X).comp (picardKerEquivCech X U hU hU₁).symm.toAddMonoidHom

/-- The value of `v` on a class: the line bundle on `X[ε]` with Čech class `c`, mapped to
`P_{X/k}(k[ε])` and then to `Pic_{X/k,(fppf)}(k[ε])`. -/
theorem coe_cohomologyToFppfPicardKer (c : structureCohomology k X 1) :
    (cohomologyToFppfPicardKer X U hU hU₁ c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      toFppfDualNumbers X ((picardKerEquivCech X U hU hU₁).symm c) :=
  rfl

/-- The inverse Čech comparison carries multiplication by `a` to pullback along `dualScale a`. -/
theorem picardKerEquivCech_symm_smul (a : k) (c : structureCohomology k X 1) :
    (picardKerEquivCech X U hU hU₁).symm (a • c) =
      dualScaleKer k X.hom a ((picardKerEquivCech X U hU hU₁).symm c) := by
  apply (picardKerEquivCech X U hU hU₁).injective
  rw [AddEquiv.apply_symm_apply, picardKerEquivCech_dualScale, AddEquiv.apply_symm_apply]

/-- **`v` is `k`-linear** (Kleiman, proof of Thm 5.11, p. 43): for the scalars `a • t = F(µ_a) t`
on `ker F(ρ)`, `v (a • c) = F(µ_a) (v c)`. -/
theorem cohomologyToFppfPicardKer_smul (a : k) (c : structureCohomology k X 1) :
    (cohomologyToFppfPicardKer X U hU hU₁ (a • c) :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom
        (cohomologyToFppfPicardKer X U hU hU₁ c) := by
  rw [coe_cohomologyToFppfPicardKer, picardKerEquivCech_symm_smul]
  exact coe_picardKerToFppf_dualScaleKer X a ((picardKerEquivCech X U hU hU₁).symm c)

/-- **`v` is injective** for `p` proper and flat with geometrically integral fibres (Kleiman,
Thm 2.5(1), p. 18, with `Pic(k[ε]) = 0`). -/
theorem cohomologyToFppfPicardKer_injective_of_isProper_of_flat_of_geometricallyIntegral
    [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Injective (cohomologyToFppfPicardKer X U hU hU₁) :=
  (picardKerToFppf_injective_of_isProper_of_flat_of_geometricallyIntegral X).comp
    (picardKerEquivCech X U hU hU₁).symm.injective

/-- With a section of `p`, `v` is the inverse of the comparison
`fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X` after the inverse Čech
comparison. -/
theorem cohomologyToFppfPicardKer_eq_symm_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    (c : structureCohomology k X 1) :
    cohomologyToFppfPicardKer X U hU hU₁ c =
      (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm
        ((picardKerEquivCech X U hU hU₁).symm c) :=
  rfl

/-- With a section of `p`, `v` is bijective (Kleiman, Thm 2.5(2), p. 18). -/
theorem
  cohomologyToFppfPicardKer_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Bijective (cohomologyToFppfPicardKer X U hU hU₁) :=
  (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm.bijective.comp
    (picardKerEquivCech X U hU hU₁).symm.bijective

end Field

end AlgebraicGeometry.Scheme.DualNumbers
