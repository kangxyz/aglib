/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Untwist
public import Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubscheme

/-!
# A Hilbert family as the closed subscheme `Z(K)` of an evaluation map

`HilbertScheme/UniversalSubscheme` defines, for `ιK : K ⟶ 𝒪_T^I` and homogeneous polynomials
`s : I → A[x]_r`, the closed subscheme `Z(K) = evaluationIdeal ι g r s ιK` of
`X_T = P^n_A ×_{Spec A} T`: the image ideal of `π^* K ⊗ 𝒪(-r) ⟶ 𝒪`. This file connects it with
the twisted ideal sheaf `I_Z(r)` of a closed subscheme `Z ⊆ X_T`:

* `familyTwistPairingIso_hom`: the pairing `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` of `HilbertScheme/IdealTwist/Untwist`
  is the pulled-back pairing `pullbackPairing` of `twistingTensorNegIso`;
* `twistedEvaluationMap_eq`: the twisted evaluation map is the evaluation
  `π^* K ⟶ p^* 𝒪_P^I ⟶ 𝒪(r)` tensored with `𝒪(-r)`, followed by that pairing;
* `evaluationIdeal_eq_of_epi`: if the evaluation `π^* K ⟶ 𝒪(r)` is an epimorphism `π^* K ⟶ I_Z(r)`
  followed by the inclusion `I_Z(r) ⟶ 𝒪(r)`, then `Z(K) = Z`;
* `IsHilbertFamily.evaluationIdeal_eq_of_epi_homEquiv`: for a point `Z` of `Hilb^Φ(T)` over a
  locally Noetherian `T` and a natural `r ≥ hilbertRegularityBound n Φ`, it suffices that the
  adjoint `K ⟶ π_* I_Z(r)` of the lift is an epimorphism (relative global generation,
  `IsHilbertFamily.epi_counit_familyIdealTwist`).

This is the form of the "⇒" inclusion of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, p. 26: `Z = Z(K)` for `K = π_* I_Z(r) ⊆ π_* 𝒪(r)`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory MvPolynomial
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- The pairing `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` on `X_T` is the pulled-back pairing of
`twistingTensorNegIso`. -/
theorem familyTwistPairingIso_hom (r : ℤ) :
    (familyTwistPairingIso ι g r).hom =
      Scheme.Modules.pullbackPairing (pullback.fst (toSpec A ι) g)
        (twistingTensorNegIso (R := A) (ι := ι) r).hom :=
  rfl

/-- **The twisted evaluation map, untwisted**: `π^* K ⊗ 𝒪(-r) ⟶ 𝒪` is the evaluation
`π^* K ⟶ p^* 𝒪_P^I ⟶ 𝒪(r)` tensored with `𝒪(-r)`, followed by the pairing
`𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`. -/
theorem twistedEvaluationMap_eq (r : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r)
    {K : T.Modules} (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) :
    twistedEvaluationMap ι g r s ιK =
      ((Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g)
          ιK ≫ (Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).map
            (homogeneousEvaluation ι r s)) ▷ familyTwistingSheaf ι g (-(r : ℤ))) ≫
        (familyTwistPairingIso ι g r).hom := by
  simp only [familyTwistPairingIso_hom, twistedEvaluationMap, Scheme.Modules.pullbackPairingOf,
    Scheme.Modules.pullbackPairing, homogeneousEvaluationPairing, Functor.map_comp,
    Category.assoc]
  simp only [Scheme.Modules.pullbackTensorMapIso_inv_naturality_assoc,
    CategoryTheory.Functor.map_id]
  refine (Scheme.Modules.tensorSheafMap_comp_assoc _ _ _ _ _ _).trans ?_
  rw [Category.id_comp]
  rfl

variable {g}

/-- **`Z(K) = Z` from an epimorphism onto `I_Z(r)`**: for a closed subscheme `Z ⊆ X_T` and
quasicoherent `K`, if the evaluation `π^* K ⟶ 𝒪(r)` of `ιK` is an epimorphism
`ψ : π^* K ⟶ I_Z(r)` followed by the inclusion `I_Z(r) ⟶ 𝒪(r)`, then `Z(K) = Z`. -/
theorem evaluationIdeal_eq_of_epi (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ)
    {I : Type u} (s : I → homogeneousSubmodule ι A r) {K : T.Modules} [K.IsQuasicoherent]
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I)
    (ψ : (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K ⟶
      familyIdealTwist ι g Z r) [Epi ψ]
    (hψ : ψ ≫ familyIdealTwistInclusion ι Z r =
      Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g)
          ιK ≫ (Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).map
            (homogeneousEvaluation ι r s)) :
    evaluationIdeal ι g r s ιK = Z := by
  rw [evaluationIdeal, twistedEvaluationMap_eq, ← hψ]
  exact imageIdealData_twistPairing_of_epi ι Z r ψ

variable {Φ : ℚ[X]} {Z : (pullback (toSpec A ι) g).IdealSheafData} (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **A Hilbert family is the closed subscheme of its evaluation map** (Nitsure,
arXiv:math/0504590v1, §5, p. 26, the "⇒" inclusion): for a point `Z` of `Hilb^Φ(T)`, `T` locally
Noetherian, a natural `r ≥ hilbertRegularityBound n Φ` and quasicoherent `K` with
`ιK : K ⟶ 𝒪_T^I`, if the evaluation `π^* K ⟶ 𝒪(r)` of `ιK` lifts to `ψ : π^* K ⟶ I_Z(r)` whose
adjoint `K ⟶ π_* I_Z(r)` is an epimorphism, then `Z(K) = Z`. -/
theorem IsHilbertFamily.evaluationIdeal_eq_of_epi_homEquiv [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {I : Type u} (s : I → homogeneousSubmodule ι A r) {K : T.Modules} [K.IsQuasicoherent]
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I)
    (ψ : (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K ⟶
      familyIdealTwist ι g Z r)
    (hψ : Epi ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd (toSpec A ι) g)).homEquiv _ _ ψ))
    (hψι : ψ ≫ familyIdealTwistInclusion ι Z r =
      Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g)
          ιK ≫ (Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).map
            (homogeneousEvaluation ι r s)) :
    evaluationIdeal ι g r s ιK = Z :=
  haveI := hZ.epi_of_epi_homEquiv ι n e r hr ψ hψ
  evaluationIdeal_eq_of_epi ι Z r s ιK ψ hψι

end AlgebraicGeometry.ProjectiveSpace
