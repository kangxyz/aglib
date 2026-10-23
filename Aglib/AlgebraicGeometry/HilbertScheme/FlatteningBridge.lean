/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Point
public import Aglib.AlgebraicGeometry.FlatteningStratification.AffineBase

/-!
# The fiber condition of the Hilbert functor in the charts of the flattening stratification

The flattening stratification over a locally Noetherian base (`FlatteningStratification/Global`)
reads the Hilbert polynomial of a module `F` on `P^n_A ×_{Spec A} T` at a point `t ∈ T` through
affine charts, `fiberHilbertPolynomialAt ι g F t`. For a point `Z` of the Hilbert functor
(`IsHilbertFamily ι Φ g Z`, Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §1, pp. 3–4) this file proves that the structure module `𝒪_Z` has
`fiberHilbertPolynomialAt ι g 𝒪_Z t = Φ` at every point
(`IsHilbertFamily.fiberHilbertPolynomialAt_quotientModule_eq`, finitely many coordinates), so that
the universal property of the strata applies to `𝒪_Z`. The chart map `affineBaseMap ι g hU` of an
affine open `U` is the point map `pointMap ι g hU.fromSpec` (`affineBaseMap_eq_pointMap`).

* `IsHilbertFamily.projectiveHilbertPolynomial_pullback_pointMap`: the module form of the fiber
  condition: the pullback of `𝒪_Z` to `P^n_K` along `pointMap ι g x` has Hilbert polynomial `Φ`
  (`quotientModulePullbackIso`, which needs no flatness).
* `fiberHilbertPolynomialAt_quotientModule_eq`: the chart fiber polynomial of `𝒪_Z` at `t` is the
  Hilbert polynomial of the fiber of `Z` at a field point over `t`, for every closed subscheme `Z`.
* `isHilbertFamily_iff_fiberHilbertPolynomialAt`: `Z ∈ Hilb^Φ(T)` iff `Z` is flat over `T` and
  `fiberHilbertPolynomialAt ι g 𝒪_Z t = Φ` for every `t ∈ T`. With the universal property
  `exists_lift_flatteningStratumι_iff_pullbackBaseChange`, which asks module flatness of `F_T`:
  `isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt` states the same with relative
  flatness of `𝒪_Z` over `T` (`relativeFlat_quotientModule_iff_flat`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) {A : Type u} [CommRing A]

variable {Φ : ℚ[X]} {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

/-- **The fiber condition in module form**: for a point `Z` of `Hilb^Φ(T)` and a field point
`x : Spec K ⟶ T`, the pullback of the structure module `𝒪_Z` to `P^n_K` has Hilbert polynomial
`Φ`. -/
theorem IsHilbertFamily.projectiveHilbertPolynomial_pullback_pointMap
    (hZ : IsHilbertFamily ι Φ g Z) (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T) :
    projectiveHilbertPolynomial K ι
      ((Scheme.Modules.pullback (pointMap ι g x)).obj Z.quotientModule) = Φ := by
  rw [projectiveHilbertPolynomial_congr K ι (Z.quotientModulePullbackIso (pointMap ι g x))]
  exact hZ.subschemeHilbertPolynomial_fiber K x

/-- **The chart fiber polynomial of `𝒪_Z` is a fiber Hilbert polynomial**: for a closed subscheme
`Z`, an affine open `U ∋ t` and the prime `p` of `Γ(T, U)` over `t`, the chart fiber polynomial of
`𝒪_Z` at `t` is the Hilbert polynomial of the fiber of `Z` at the field point
`Spec κ(p) ⟶ Spec Γ(T, U) ⟶ T`. -/
theorem fiberHilbertPolynomialAt_quotientModule_eq [Finite ι] {U : T.Opens} (hU : IsAffineOpen U)
    (t : T) (htU : t ∈ U) :
    fiberHilbertPolynomialAt ι g Z.quotientModule t =
      subschemeHilbertPolynomial ι (hU.primeIdealOf ⟨t, htU⟩).asIdeal.ResidueField
        (Z.comap (pointMap ι g (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U)
          (hU.primeIdealOf ⟨t, htU⟩).asIdeal.ResidueField)) ≫ hU.fromSpec))) := by
  have := Z.quotientModule_isQuasicoherent
  rw [fiberHilbertPolynomialAt_eq ι g Z.quotientModule hU t htU]
  let p := hU.primeIdealOf ⟨t, htU⟩
  let x := Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) p.asIdeal.ResidueField)) ≫ hU.fromSpec
  have e1 : (Scheme.Modules.pullback (map (algebraMap Γ(T, U) p.asIdeal.ResidueField) ι)).obj
      (affineBaseModule ι g Z.quotientModule hU) ≅
      (Scheme.Modules.pullback (pointMap ι g x)).obj Z.quotientModule :=
    (Scheme.Modules.pullbackComp (map (algebraMap Γ(T, U) p.asIdeal.ResidueField) ι)
      (affineBaseMap ι g hU)).app Z.quotientModule ≪≫
      (Scheme.Modules.pullbackCongr (by rw [affineBaseMap_eq_pointMap, map_comp_pointMap])).app
        Z.quotientModule
  change projectiveHilbertPolynomial p.asIdeal.ResidueField ι
    ((Scheme.Modules.pullback (map (algebraMap Γ(T, U) p.asIdeal.ResidueField) ι)).obj
      (affineBaseModule ι g Z.quotientModule hU)) = _
  rw [projectiveHilbertPolynomial_congr _ ι e1, projectiveHilbertPolynomial_congr _ ι
    (Z.quotientModulePullbackIso (pointMap ι g x))]
  rfl

/-- **The fiber condition in the charts of the flattening stratification**: for a point `Z` of
`Hilb^Φ(T)`, the structure module `𝒪_Z` on `P^n_A ×_{Spec A} T` has
`fiberHilbertPolynomialAt ι g 𝒪_Z t = Φ` at every point `t ∈ T`. -/
theorem IsHilbertFamily.fiberHilbertPolynomialAt_quotientModule_eq [Finite ι]
    (hZ : IsHilbertFamily ι Φ g Z) (t : T) :
    fiberHilbertPolynomialAt ι g Z.quotientModule t = Φ := by
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top t)
  rw [ProjectiveSpace.fiberHilbertPolynomialAt_quotientModule_eq ι hU t htU]
  exact hZ.subschemeHilbertPolynomial_fiber _ _

/-- **The Hilbert functor in the language of the flattening stratification**: for finitely many
coordinates, `Z` is a point of `Hilb^Φ(T)` if and only if `Z` is flat over `T` and the chart fiber
polynomial of `𝒪_Z` is `Φ` at every point of `T`. -/
theorem isHilbertFamily_iff_fiberHilbertPolynomialAt [Finite ι] :
    IsHilbertFamily ι Φ g Z ↔ Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) ∧
      ∀ t : T, fiberHilbertPolynomialAt ι g Z.quotientModule t = Φ := by
  refine ⟨fun hZ => ⟨hZ.flat, hZ.fiberHilbertPolynomialAt_quotientModule_eq ι⟩,
    fun ⟨hflat, h⟩ => ?_⟩
  refine (isHilbertFamily_iff_residueField ι Z).mpr ⟨hflat, fun t => ?_⟩
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top t)
  have ht := h t
  rw [fiberHilbertPolynomialAt_quotientModule_eq ι hU t htU] at ht
  obtain ⟨p, hp⟩ : ∃ p, hU.primeIdealOf ⟨t, htU⟩ = p := ⟨_, rfl⟩
  have hpt : hU.fromSpec p = t := hp ▸ hU.fromSpec_primeIdealOf ⟨t, htU⟩
  rw [hp] at ht
  obtain ⟨⟨t', ψ⟩, hx⟩ : ∃ y, (Scheme.SpecToEquivOfField p.asIdeal.ResidueField T).symm y =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) p.asIdeal.ResidueField)) ≫ hU.fromSpec :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) p.asIdeal.ResidueField))
      (IsLocalRing.closedPoint p.asIdeal.ResidueField) = p := by
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal p.asIdeal.ResidueField).comap
      (algebraMap Γ(T, U) p.asIdeal.ResidueField) = p.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
      Ideal.ker_algebraMap_residueField]
  have ht' : t' = t := by
    have h₁ : ((Scheme.SpecToEquivOfField p.asIdeal.ResidueField T)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) p.asIdeal.ResidueField)) ≫
          hU.fromSpec)).1 = t' := by
      rw [← hx, Equiv.apply_symm_apply]
    rw [← h₁]
    change hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) p.asIdeal.ResidueField))
      (IsLocalRing.closedPoint p.asIdeal.ResidueField)) = t
    rw [h₂, hpt]
  subst ht'
  rw [← hx, Scheme.SpecToEquivOfField_symm_apply, ← CommRingCat.ofHom_hom ψ,
    ← map_comp_pointMap, Scheme.IdealSheafData.comap_comp,
    subschemeHilbertPolynomial_comap_map] at ht
  exact ht

/-- **The Hilbert functor in the form of the universal property of the flattening strata**: for
finitely many coordinates, `Z` is a point of `Hilb^Φ(T)` if and only if its structure module
`𝒪_Z` on `P^n_A ×_{Spec A} T` is relatively flat over `T` with chart fiber polynomial `Φ` at every
point; this is the right-hand side of `exists_lift_flatteningStratumι_iff_pullbackBaseChange` for
`F_T = 𝒪_Z`. -/
theorem isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt [Finite ι] :
    IsHilbertFamily ι Φ g Z ↔ Scheme.Modules.relativeFlat (pullback.snd (toSpec A ι) g)
        Z.quotientModule ∧
      ∀ t : T, fiberHilbertPolynomialAt ι g Z.quotientModule t = Φ := by
  rw [isHilbertFamily_iff_fiberHilbertPolynomialAt,
    Scheme.IdealSheafData.relativeFlat_quotientModule_iff_flat]

end ProjectiveSpace

end AlgebraicGeometry
