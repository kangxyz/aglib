/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Kaehler

/-!
# The original conormal map at a smooth localization

Localization of the intrinsic first cotangent homology, together with flat
exactness, makes the original presentation's conormal map injective at a
formally smooth localization. The coordinates of this same map are the
original polynomial partial derivatives. No replacement standard-smooth
chart or inversion of a nonunit formal value is used.
-/

@[expose] public section

noncomputable section

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R B K σ : Type*} [CommRing R] [CommRing B] [CommRing K]
  [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]

/-- At a formally smooth localization, the base change of the original
presentation's conormal map is injective. -/
theorem cotangentComplex_baseChange_injective_of_formallySmooth_localization
    (P : Generators R B σ) (M : Submonoid B) [IsLocalization M K]
    [Algebra.FormallySmooth R K] :
    Function.Injective (P.toExtension.cotangentComplex.baseChange K) := by
  let e : K ⊗[B] P.toExtension.H1Cotangent ≃ₗ[K] Algebra.H1Cotangent R K :=
    (P.equivH1Cotangent.baseChange B K _ _).trans
      (Algebra.tensorH1CotangentOfIsLocalization R K M)
  have : Subsingleton (K ⊗[B] P.toExtension.H1Cotangent) := e.subsingleton
  let : Module.Flat B K := IsLocalization.flat K M
  have hex : Function.Exact (P.toExtension.h1Cotangentι.baseChange K)
      (P.toExtension.cotangentComplex.baseChange K) :=
    Module.Flat.lTensor_exact K P.toExtension.exact_hCotangentι_cotangentComplex
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := (hex x).mp hx
  rw [Subsingleton.elim z 0, map_zero]

omit [Algebra R K] [IsScalarTower R B K] in
/-- The original conormal map remains injective after any further scalar
extension of a smooth localization. Projectivity of its localized cokernel
provides an actual splitting before this possibly nonflat extension. -/
theorem cotangentComplex_baseChange_injective_of_formallySmooth_localization_tower
    {L : Type*} [CommRing L] [Algebra R L] [Algebra B L] [IsScalarTower R B L]
    [Algebra L K] [IsScalarTower B L K]
    (P : Generators R B σ) (M : Submonoid B) [IsLocalization M L]
    [Algebra.FormallySmooth R L] :
    Function.Injective (P.toExtension.cotangentComplex.baseChange K) := by
  let f := P.toExtension.cotangentComplex.baseChange L
  let g := P.toExtension.toKaehler.baseChange L
  let : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization M
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B L
  let : Module.Projective L (L ⊗[B] KaehlerDifferential R B) :=
    Module.Projective.of_equiv e.symm
  let : Module.Flat B L := IsLocalization.flat L M
  have hf : Function.Injective f :=
    P.cotangentComplex_baseChange_injective_of_formallySmooth_localization M
  have hg : Function.Surjective g :=
    LinearMap.lTensor_surjective L P.toExtension.toKaehler_surjective
  have hex : Function.Exact f g :=
    Module.Flat.lTensor_exact L P.toExtension.exact_cotangentComplex_toKaehler
  obtain ⟨l, hl⟩ := ((hex.split_tfae'.out 1 2 rfl rfl).mp
    ⟨hf, Module.projective_lifting_property g LinearMap.id hg⟩).2
  have hleft : (l.baseChange K).comp (f.baseChange K) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
  have hfi : Function.Injective (f.baseChange K) :=
    (show Function.LeftInverse (l.baseChange K) (f.baseChange K) from
      fun x => LinearMap.congr_fun hleft x).injective
  let eM := AlgebraTensorModule.cancelBaseChange B L K K P.toExtension.Cotangent
  let eN := AlgebraTensorModule.cancelBaseChange B L K K P.toExtension.CotangentSpace
  intro x y hxy
  apply eM.symm.injective
  apply hfi
  simpa only [f, eM, eN, LinearMap.baseChange_baseChange, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using congrArg eN.symm hxy

omit [Algebra R K] [IsScalarTower R B K] in
/-- The localized original conormal map has the literal evaluated partial
 derivatives as its coordinates in the base-changed polynomial basis. -/
theorem cotangentSpaceBasis_baseChange_repr_cotangentComplex_mk
    (P : Generators R B σ) (f : P.ker) (j : σ) :
    (P.cotangentSpaceBasis.baseChange K).repr
      ((P.toExtension.cotangentComplex.baseChange K)
        ((1 : K) ⊗ₜ[B] Algebra.Extension.Cotangent.mk f)) j =
      algebraMap B K (aeval P.val (pderiv j f.val)) := by
  simp only [LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]
  congr 1
  change P.cotangentSpaceBasis.repr
    ((1 : B) ⊗ₜ[P.toExtension.Ring] KaehlerDifferential.D R P.toExtension.Ring f.val) j = _
  exact P.cotangentSpaceBasis_repr_one_tmul f.val j

end Algebra.Generators
