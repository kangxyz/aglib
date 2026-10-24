/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.FieldSection
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.QuasiCompactSeparated
public import Aglib.AlgebraicGeometry.Picard.BaseChange
public import Aglib.AlgebraicGeometry.Picard.Tangent.FieldExtension

/-!
# The tangent space at the unit of the Picard scheme is `H^1(X, 𝒪_X)`

Let `k` be a field and `X : FScheme k` with structure morphism `p` proper and flat with
geometrically integral fibres. Let `F = Pic_{X/k,(fppf)}` (`(fppfPicardSheaf p).obj`), and let
`e` be a representation of the restriction of `F` to locally Noetherian test schemes by
`P : Scheme.LocallyNoetherianOver (Spec k)` (an explicit argument). Then

* `tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e :
  ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)`, for the `k`-structure `a • t = F(µ_a) t` of
  `tangentKernelModule e k`; its inverse is Kleiman's map `v`
  (`tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral_symm_apply`);
* `cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e :
  (𝔪/𝔪²)^∨ ≃ₗ[k] H^1(X, 𝒪_X)`, for the maximal ideal `𝔪` of the local ring of `P` at the unit
  point (the Zariski tangent space);
* `finrank_structureH1_eq_finrank_cotangentSpace_of_isProper_of_flat_of_geometricallyIntegral X e`:
  `finrank_k H^1(X, 𝒪_X) = finrank_k (𝔪/𝔪²)`; both are finite (`finite_tangentKernel`, and
  Kleiman's `v` embeds `H^1(X, 𝒪_X)` into the finite tangent kernel).

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 5.11, p. 42:
`T_0 Pic_{X/k} = H^1(𝒪_X)`, in the fppf form on locally Noetherian test schemes; Kleiman assumes
that `Pic_{X/k}` represents the étale sheaf.

## Proof

1. Kleiman's `v : H^1(X, 𝒪_X) → ker(F(k[ε]) → F(k))` (proof of Thm 5.11, p. 43;
   `DualNumbers.cohomologyToFppfPicardKer`) is injective (Thm 2.5(1), p. 18) and `k`-linear;
   through `tangentKernel_eq_ker_closedPointOver` and `specOverMap_map_smul_id_eq_scaleOver`
   it is the `k`-linear map `structureCohomologyToTangentKernel`.
2. Let `K` be a field over `k` such that the base change `X_K ⟶ Spec K` has a section, for
   example a residue field of `X` (`Cohomology.exists_isSplitEpi_fieldBaseChange_hom`). Then
   `v_K` for `X_K` is bijective (Thm 2.5(2), p. 18). Composed with the base change of `F`
   (Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65; `fppfPicardSheafBaseChangeKerAddEquiv`) and
   with `kerClosedPointOverAddEquivTangentKernel`, it gives
   `ker(F(K[ε]) → F(K)) ≃ₗ[K] H^1(X_K, 𝒪)`
   (`tangentKernelLinearEquivFieldBaseChangeOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`).
3. Dimensions: `finrank_k H^1(X, 𝒪_X) = finrank_K H^1(X_K, 𝒪)` by flat base change of
   cohomology (`structureCohomologyBaseChangeMap_bijective_of_isProper`), which is
   `finrank_K ker(F(K[ε]) → F(K)) = finrank_k (𝔪/𝔪²)` by step 2 and the rank formula
   `finrank_tangentKernel` at `L = K`; the same formula at `L = k` gives
   `finrank_k ker(F(k[ε]) → F(k))`, which is finite (`finite_tangentKernel`).
4. An injective `k`-linear map between spaces of the same finite dimension is bijective.

Kleiman base changes Square (5.11.4) to an algebraically closed field and identifies
`T_0 Pic_{X/k} ⊗_k K` with `T_0 Pic_{X_K/K}` (pp. 43–44), and he uses Exercise 2.3 for the
vertical maps (p. 44). Here only dimensions are compared, any field `K` over which `X` acquires a
section serves, and the vertical maps are bijective by Thm 2.5(2). No group scheme structure and
no finite-type or separatedness hypothesis on `P` is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.DualNumbers
  (cohomologyToFppfPicardKer_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {k : Type u} [Field k] (X : FScheme k)
  {P : LocallyNoetherianOver (Spec (.of k))}
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

section FieldExtension

variable (K : Type u) [Field K] [Algebra k K]

/-- **Base change of the tangent kernel of the Picard sheaf, compatibly with `µ_a`**: the
equivalence `fppfPicardSheafBaseChangeKerAddEquiv` at the closed point of `K[ε]` carries
`Pic_{X_K/K,(fppf)}(scaleOver K a)` to `Pic_{X/k,(fppf)}` of `scaleOver K a` viewed over
`Spec k` (Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65, naturally in the test scheme). -/
theorem fppfPicardSheafBaseChangeKerAddEquiv_map_scaleOver (a : K)
    (y y' : ((fppfPicardSheaf (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj.map
        (DualNumbers.closedPointOver K).op).hom.ker)
    (h : (y' : (fppfPicardSheaf (pullback.snd X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj.obj
          (op (Over.mk (DualNumbers.dualMap K)))) =
      ((fppfPicardSheaf (pullback.snd X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj.map
          (DualNumbers.scaleOver K a).op).hom y) :
    (fppfPicardSheafBaseChangeKerAddEquiv X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (DualNumbers.closedPointOver K) y' :
        (fppfPicardSheaf X.hom).obj.obj (op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).obj (Over.mk (DualNumbers.dualMap K))))) =
      ((fppfPicardSheaf X.hom).obj.map ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).map (DualNumbers.scaleOver K a)).op).hom
        (fppfPicardSheafBaseChangeKerAddEquiv X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (DualNumbers.closedPointOver K) y) := by
  rw [fppfPicardSheafBaseChangeKerAddEquiv_apply_coe,
    fppfPicardSheafBaseChangeKerAddEquiv_apply_coe, h]
  exact fppfPicardSheafBaseChangeIso_hom_app_map_apply X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) (DualNumbers.scaleOver K a) y

variable [(fieldBaseChange K X).left.IsSeparated] {ι : Type u}
  (U : ι → (fieldBaseChange K X).left.Opens) (hU : iSup U = ⊤) (hU₁ : ∀ j, IsAffineOpen (U j))
  [IsSplitEpi (fieldBaseChange K X).hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

/-- **The tangent kernel over a field extension with a section**: if `X_K ⟶ Spec K` has a
section, `ker(F(K[ε]) → F(K)) ≃ₗ[K] H^1(X_K, 𝒪)` for `F = Pic_{X/k,(fppf)}` and the scalars
`a • t = F(µ_a) t`. The inverse is Kleiman's map `v_K` for `X_K` (proof of Thm 5.11, p. 43),
bijective by Thm 2.5(2) (p. 18) since `X_K` has a section, followed by the base change of the
Picard sheaf (Ex. 4.4, p. 27, and Answer 4.4, p. 65) and `kerClosedPointOverAddEquivTangentKernel`
(`linearEquivTangentKernelOfFieldExtension`). -/
def tangentKernelLinearEquivFieldBaseChangeOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral :
    letI := tangentKernelModule e K
    tangentKernel (fppfPicardSheaf X.hom).obj K ≃ₗ[K]
      structureCohomology K (fieldBaseChange K X) 1 :=
  haveI : IsProper (fieldBaseChange K X).hom := inferInstanceAs
    (IsProper (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  haveI : Flat (fieldBaseChange K X).hom := inferInstanceAs
    (Flat (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  haveI : GeometricallyIntegral (fieldBaseChange K X).hom := inferInstanceAs
    (GeometricallyIntegral (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  linearEquivTangentKernelOfFieldExtension e
    (fppfPicardSheaf (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
    (fppfPicardSheafBaseChangeKerAddEquiv X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (DualNumbers.closedPointOver K))
    (fppfPicardSheafBaseChangeKerAddEquiv_map_scaleOver X K)
    (DualNumbers.cohomologyToFppfPicardKer (fieldBaseChange K X) U hU hU₁)
    (DualNumbers.cohomologyToFppfPicardKer_smul (fieldBaseChange K X) U hU hU₁)
    (cohomologyToFppfPicardKer_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
      (fieldBaseChange K X) U hU hU₁)

end FieldExtension

section Field

variable [X.left.IsSeparated] {ι : Type u} (U : ι → X.left.Opens) (hU : iSup U = ⊤)
  (hU₁ : ∀ j, IsAffineOpen (U j))

/-- **Kleiman's map `v : H^1(X, 𝒪_X) → T_0`** (proof of Thm 5.11, p. 43) as a `k`-linear map
into `ker(F(k[ε]) → F(k))` with the scalars `a • t = F(µ_a) t`:
`DualNumbers.cohomologyToFppfPicardKer`, viewed in `tangentKernel` (`linearMapToTangentKernel`). -/
def structureCohomologyToTangentKernel :
    letI := tangentKernelModule e k
    structureCohomology k X 1 →ₗ[k] tangentKernel (fppfPicardSheaf X.hom).obj k :=
  linearMapToTangentKernel (fppfPicardSheaf X.hom).obj e
    (DualNumbers.cohomologyToFppfPicardKer X U hU hU₁)
    (DualNumbers.cohomologyToFppfPicardKer_smul X U hU hU₁)

/-- The value of `structureCohomologyToTangentKernel` is Kleiman's `v`. -/
theorem coe_structureCohomologyToTangentKernel_apply (c : structureCohomology k X 1) :
    (structureCohomologyToTangentKernel X e U hU hU₁ c :
        (fppfPicardSheaf X.hom).obj.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (DualNumbers.cohomologyToFppfPicardKer X U hU hU₁ c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (DualNumbers.dualMap k)))) :=
  coe_linearMapToTangentKernel_apply _ e _ _ c

/-- `v` is injective (Kleiman, Thm 2.5(1), p. 18). -/
theorem structureCohomologyToTangentKernel_injective_of_isProper_of_flat_of_geometricallyIntegral
    [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Injective (structureCohomologyToTangentKernel X e U hU hU₁) :=
  linearMapToTangentKernel_injective _ e _ _
    (DualNumbers.cohomologyToFppfPicardKer_injective_of_isProper_of_flat_of_geometricallyIntegral
      X U hU hU₁)

end Field

section Dimension

variable [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

/-- **The dimension of `H^1(X, 𝒪_X)`, with a field extension giving a section**: if
`X_K ⟶ Spec K` has a section for a field `K` over `k`, then
`finrank_k H^1(X, 𝒪_X) = finrank_k (𝔪/𝔪²)` for the local ring of `P` at the unit point. -/
private theorem finrank_structureH1_eq_finrank_cotangentSpace_of_isSplitEpi (K : Type u)
    [Field K] [Algebra k K] [IsSplitEpi (fieldBaseChange K X).hom] :
    Module.finrank k (structureCohomology k X 1) =
      Module.finrank k (CotangentSpace (unitStalk e)) := by
  have : IsSeparated (fieldBaseChange K X).hom := inferInstanceAs
    (IsSeparated (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  have : (fieldBaseChange K X).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (fieldBaseChange K X).hom]
    infer_instance⟩
  have : Module.Free k (structureCohomology k X 1) := Module.Free.of_divisionRing k _
  let := tangentKernelModule e K
  calc Module.finrank k (structureCohomology k X 1)
      = Module.finrank K (K ⊗[k] structureCohomology k X 1) :=
        (Module.finrank_baseChange (R := K) (S := k)).symm
    _ = Module.finrank K (structureCohomology K (fieldBaseChange K X) 1) :=
        (LinearEquiv.ofBijective _
          (structureCohomologyBaseChangeMap_bijective_of_isProper K X 1)).finrank_eq
    _ = Module.finrank K (tangentKernel (fppfPicardSheaf X.hom).obj K) :=
        (tangentKernelLinearEquivFieldBaseChangeOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral
          X e K
          (fun j : (fieldBaseChange K X).left.affineOpens => (j : (fieldBaseChange K X).left.Opens))
          (iSup_affineOpens_eq_top _) (fun j => j.2)).finrank_eq.symm
    _ = Module.finrank k (CotangentSpace (unitStalk e)) := finrank_tangentKernel e K

/-- **`dim_k H^1(X, 𝒪_X)` is the embedding dimension of `P` at the unit**:
`finrank_k H^1(X, 𝒪_X) = finrank_k (𝔪/𝔪²)`. The proof base changes to a residue field of `X`
(`Cohomology.exists_isSplitEpi_fieldBaseChange_hom`). -/
theorem
  finrank_structureH1_eq_finrank_cotangentSpace_of_isProper_of_flat_of_geometricallyIntegral :
    Module.finrank k (structureCohomology k X 1) =
      Module.finrank k (CotangentSpace (unitStalk e)) := by
  obtain ⟨x, -⟩ := X.hom.surjective (closedPoint (CommRingCat.of k))
  obtain ⟨K, _, _, _⟩ := exists_isSplitEpi_fieldBaseChange_hom X x
  exact finrank_structureH1_eq_finrank_cotangentSpace_of_isSplitEpi X e K

include e in
/-- **`H^1(X, 𝒪_X)` is finite-dimensional**, since `v` embeds it into the finite-dimensional
tangent kernel `ker(F(k[ε]) → F(k))`. -/
private theorem finite_structureCohomology_one : Module.Finite k (structureCohomology k X 1) := by
  have : X.left.IsSeparated := ⟨by rw [← terminal.comp_from X.hom]; infer_instance⟩
  let := tangentKernelModule e k
  have := finite_tangentKernel e k
  exact FiniteDimensional.of_injective
    (structureCohomologyToTangentKernel X e (fun j : X.left.affineOpens => (j : X.left.Opens))
      (iSup_affineOpens_eq_top _) (fun j => j.2))
    (structureCohomologyToTangentKernel_injective_of_isProper_of_flat_of_geometricallyIntegral
      X e _ _ _)

end Dimension

section Bijective

variable [X.left.IsSeparated] {ι : Type u} (U : ι → X.left.Opens) (hU : iSup U = ⊤)
  (hU₁ : ∀ j, IsAffineOpen (U j)) [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

/-- **`v` is bijective**: it is injective and `k`-linear between spaces of the same finite
dimension `finrank_k (𝔪/𝔪²)`. -/
theorem structureCohomologyToTangentKernel_bijective_of_isProper_of_flat_of_geometricallyIntegral :
    Function.Bijective (structureCohomologyToTangentKernel X e U hU hU₁) := by
  let := tangentKernelModule e k
  have := finite_tangentKernel e k
  have := finite_structureCohomology_one X e
  refine ⟨structureCohomologyToTangentKernel_injective_of_isProper_of_flat_of_geometricallyIntegral
      X e U hU hU₁,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
      (structureCohomologyToTangentKernel_injective_of_isProper_of_flat_of_geometricallyIntegral
        X e U hU hU₁)⟩
  rw [finrank_structureH1_eq_finrank_cotangentSpace_of_isProper_of_flat_of_geometricallyIntegral
      X e, finrank_tangentKernel e k]

end Bijective

section Endpoint

variable [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

/-- **The tangent space at the unit of the Picard scheme is `H^1(X, 𝒪_X)`** (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Thm 5.11, p. 42): for `X` proper and flat over a field `k` with
geometrically integral fibres and `Pic_{X/k,(fppf)}` represented on locally Noetherian test
schemes, `ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)` for the scalars `a • t = F(µ_a) t`. The inverse
is Kleiman's `v` on the cover of `X` by all its affine opens. -/
def tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral :
    letI := tangentKernelModule e k
    tangentKernel (fppfPicardSheaf X.hom).obj k ≃ₗ[k] structureCohomology k X 1 :=
  letI := tangentKernelModule e k
  haveI : X.left.IsSeparated := ⟨by rw [← terminal.comp_from X.hom]; infer_instance⟩
  (LinearEquiv.ofBijective
    (structureCohomologyToTangentKernel X e (fun j : X.left.affineOpens => (j : X.left.Opens))
      (iSup_affineOpens_eq_top _) (fun j => j.2))
    (structureCohomologyToTangentKernel_bijective_of_isProper_of_flat_of_geometricallyIntegral
      X e _ _ _)).symm

/-- The inverse of
`tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral` is Kleiman's
`v` on the cover by all affine opens. -/
theorem
  tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral_symm_apply
    [X.left.IsSeparated] (c : structureCohomology k X 1) :
    ((tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
        X e).symm c :
        (fppfPicardSheaf X.hom).obj.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (DualNumbers.cohomologyToFppfPicardKer X (fun j : X.left.affineOpens => (j : X.left.Opens))
        (iSup_affineOpens_eq_top _) (fun j => j.2) c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (DualNumbers.dualMap k)))) :=
  coe_structureCohomologyToTangentKernel_apply X e _ _ _ c

/-- **The Zariski form** (Kleiman, proof of Thm 5.11, p. 42, first paragraph): the dual of the
cotangent space `𝔪/𝔪²` of `P` at the unit point is `H^1(X, 𝒪_X)`. -/
def cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral :
    Module.Dual k (CotangentSpace (unitStalk e)) ≃ₗ[k] structureCohomology k X 1 :=
  letI := tangentKernelModule e k
  (tangentKernelLinearEquiv e k).symm ≪≫ₗ
    tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e

end Endpoint

end AlgebraicGeometry.Scheme.RelativePicard
