/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.GlobalGeneration
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Hom
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Aglib.CategoryTheory.Monoidal.Untwist

/-!
# The ideal of a Hilbert family as the image of `π^* π_* I_Z(r) ⊗ 𝒪(-r) ⟶ 𝒪`

On `X_T = P^n_A ×_{Spec A} T`, with `p = pullback.fst` and `π = pullback.snd`:

* `familyTwistPairingIso ι g r : 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`, the pullback along `p` of
  `twistingTensorNegIso` (through the tensor comparison and `pullbackUnitIso`);
* `familyIdealTwistInclusion ι g Z r : I_Z(r) ⟶ 𝒪(r)`, the twist of `I_Z ⟶ 𝒪` followed by the
  right unitor;
* `familyIdealUntwistIso ι g Z r : I_Z(r) ⊗ 𝒪(-r) ≅ I_Z` (`untwistIso`), with
  `familyIdealUntwistIso_hom_idealInclusion`: followed by `I_Z ⟶ 𝒪` it is the inclusion into
  `𝒪(r)` tensored with `𝒪(-r)`, followed by the pairing.

Hence, for every epimorphism `ψ : P ⟶ I_Z(r)` from a quasicoherent module, the image ideal of
`P ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` is `Z` (`imageIdealData_twistPairing_of_epi`; no hypothesis on
`Z`). For a point `Z` of `Hilb^Φ(T)` over a locally Noetherian `T` and a natural
`r ≥ hilbertRegularityBound n Φ`, the counit `π^* π_* I_Z(r) ⟶ I_Z(r)` is such an epimorphism
(`IsHilbertFamily.epi_counit_familyIdealTwist`), so
`IsHilbertFamily.imageIdealData_twistPairing_counit`: **`I_Z` is the image of
`π^* π_* I_Z(r) ⊗ 𝒪(-r) ⟶ 𝒪`** (Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, p. 26, "Embedding Quot into Grassmannian": the image of `h`, twisted by
`-r`). More generally a map `ψ : π^* K ⟶ I_Z(r)` is an
epimorphism as soon as its adjoint `K ⟶ π_* I_Z(r)` is (`IsHilbertFamily.epi_of_epi_homEquiv`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules.QuasiCoherent

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

-- The tensor comparison and the negative-twist isomorphism are stated through `tensorSheaf` and
-- `moduleTensorLeftFunctor`, which agree with the monoidal tensor only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- **The pairing `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` on `X_T`**: the pullback along the first projection of
`twistingTensorNegIso`, through the tensor comparison `pullbackTensorMap` and `pullbackUnitIso`. -/
def familyTwistPairingIso (r : ℤ) :
    familyTwistingSheaf ι g r ⊗ familyTwistingSheaf ι g (-r) ≅
      𝟙_ (pullback (toSpec A ι) g).Modules :=
  haveI := Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso (pullback.fst (toSpec A ι) g)
    (twistingSheaf A ι r) (twistingSheaf A ι (-r))
  (asIso (Scheme.Modules.pullbackTensorMap (pullback.fst (toSpec A ι) g) (twistingSheaf A ι r)
      (twistingSheaf A ι (-r)))).symm ≪≫
    (Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).mapIso
        (twistingTensorNegIso (R := A) (ι := ι) r) ≪≫
      Scheme.Modules.pullbackUnitIso (pullback.fst (toSpec A ι) g)

variable {g}

/-- The inclusion `I_Z(r) ⟶ 𝒪(r)` on `X_T`: `𝒪(r) ◁ (I_Z ⟶ 𝒪)` followed by the right unitor. -/
def familyIdealTwistInclusion (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    familyIdealTwist ι g Z r ⟶ familyTwistingSheaf ι g r :=
  (familyTwistingSheaf ι g r ◁ Scheme.Hom.idealInclusion Z.subschemeι) ≫ (ρ_ _).hom

/-- **Untwisting `I_Z(r)`**: `I_Z(r) ⊗ 𝒪(-r) = (𝒪(r) ⊗ I_Z) ⊗ 𝒪(-r) ≅ I_Z` through the pairing
`familyTwistPairingIso` (`untwistIso`). -/
def familyIdealUntwistIso (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    familyIdealTwist ι g Z r ⊗ familyTwistingSheaf ι g (-r) ≅
      Scheme.Hom.idealModule Z.subschemeι :=
  untwistIso (familyTwistPairingIso ι g r) _

/-- The untwisting followed by `I_Z ⟶ 𝒪` is the inclusion `I_Z(r) ⟶ 𝒪(r)` tensored with `𝒪(-r)`,
followed by the pairing `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` (`untwistIso_hom_comp`). -/
theorem familyIdealUntwistIso_hom_idealInclusion (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (r : ℤ) :
    (familyIdealUntwistIso ι Z r).hom ≫ Scheme.Hom.idealInclusion Z.subschemeι =
      (familyIdealTwistInclusion ι Z r ▷ familyTwistingSheaf ι g (-r)) ≫
        (familyTwistPairingIso ι g r).hom :=
  untwistIso_hom_comp _ _

/-- **Lifting to `I_Z(r)`**: a map `j : P ⟶ 𝒪(r)` whose restriction
`P ⟶ 𝒪(r) ≅ 𝒪(r) ⊗ 𝒪 ⟶ 𝒪(r) ⊗ 𝒪_Z` vanishes factors through `I_Z(r)`, by the exactness of the
twisted sequence (`familyTwistedShortComplex_shortExact`). -/
def familyIdealTwistLift (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ)
    {P : (pullback (toSpec A ι) g).Modules} (j : P ⟶ familyTwistingSheaf ι g r)
    (hj : j ≫ (ρ_ (familyTwistingSheaf ι g r)).inv ≫
      (familyTwistedShortComplex ι g Z r).g = 0) :
    P ⟶ familyIdealTwist ι g Z r :=
  haveI := (familyTwistedShortComplex_shortExact ι Z r).mono_f
  (familyTwistedShortComplex_shortExact ι Z r).exact.lift (j ≫ (ρ_ _).inv)
    ((Category.assoc _ _ _).trans hj)

/-- The lift of `j` to `I_Z(r)` followed by the inclusion `I_Z(r) ⟶ 𝒪(r)` is `j`. -/
@[reassoc]
theorem familyIdealTwistLift_inclusion (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ)
    {P : (pullback (toSpec A ι) g).Modules} (j : P ⟶ familyTwistingSheaf ι g r)
    (hj : j ≫ (ρ_ (familyTwistingSheaf ι g r)).inv ≫
      (familyTwistedShortComplex ι g Z r).g = 0) :
    familyIdealTwistLift ι Z r j hj ≫ familyIdealTwistInclusion ι Z r = j := by
  have h : familyIdealTwistLift ι Z r j hj ≫ (familyTwistedShortComplex ι g Z r).f =
      j ≫ (ρ_ _).inv := by
    have := (familyTwistedShortComplex_shortExact ι Z r).mono_f
    exact (familyTwistedShortComplex_shortExact ι Z r).exact.lift_f _ _
  calc familyIdealTwistLift ι Z r j hj ≫ familyIdealTwistInclusion ι Z r
      = (familyIdealTwistLift ι Z r j hj ≫ (familyTwistedShortComplex ι g Z r).f) ≫
          (ρ_ _).hom := (Category.assoc _ _ _).symm
    _ = (j ≫ (ρ_ _).inv) ≫ (ρ_ _).hom := congrArg (· ≫ (ρ_ _).hom) h
    _ = j := (Category.assoc _ _ _).trans (by rw [Iso.inv_hom_id, Category.comp_id])

/-- **The image of an epimorphism onto `I_Z(r)`, untwisted**: for a closed subscheme `Z ⊆ X_T` and
an epimorphism `ψ : P ⟶ I_Z(r)` from a quasicoherent module, the image ideal of
`P ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` is `Z`. No hypothesis on `Z` is needed. -/
theorem imageIdealData_twistPairing_of_epi (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (r : ℤ) {P : (pullback (toSpec A ι) g).Modules} [P.IsQuasicoherent]
    (ψ : P ⟶ familyIdealTwist ι g Z r) [Epi ψ] :
    Scheme.Modules.Hom.imageIdealData
      (((ψ ≫ familyIdealTwistInclusion ι Z r) ▷ familyTwistingSheaf ι g (-r)) ≫
        (familyTwistPairingIso ι g r).hom) = Z := by
  have : PreservesFiniteColimits
      (Scheme.Modules.moduleTensorRightFunctor _ (familyTwistingSheaf ι g (-r))) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have : Epi (ψ ▷ familyTwistingSheaf ι g (-r)) :=
    inferInstanceAs (Epi ((Scheme.Modules.moduleTensorRightFunctor _
      (familyTwistingSheaf ι g (-r))).map ψ))
  have : (P ⊗ familyTwistingSheaf ι g (-r)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_moduleTensorLeftFunctor _ _
  have h : ((ψ ≫ familyIdealTwistInclusion ι Z r) ▷ familyTwistingSheaf ι g (-r)) ≫
      (familyTwistPairingIso ι g r).hom =
    ((ψ ▷ familyTwistingSheaf ι g (-r)) ≫ (familyIdealUntwistIso ι Z r).hom) ≫
      Scheme.Hom.idealInclusion Z.subschemeι := by
    rw [comp_whiskerRight, Category.assoc, Category.assoc,
      familyIdealUntwistIso_hom_idealInclusion]
  rw [h]
  exact Scheme.Modules.Hom.imageIdealData_eq_of_epi_comp
    (Scheme.Modules.Hom.imageIdealLocalizes_of_isQuasicoherent _) Z _ rfl

variable {Φ : ℚ[X]} {Z : (pullback (toSpec A ι) g).IdealSheafData} (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- A map `ψ : π^* K ⟶ I_Z(r)` is an epimorphism when its adjoint `K ⟶ π_* I_Z(r)` is: `ψ` is the
pullback of its adjoint followed by the counit, which is an epimorphism
(`IsHilbertFamily.epi_counit_familyIdealTwist`). -/
theorem IsHilbertFamily.epi_of_epi_homEquiv [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) {K : T.Modules}
    (ψ : (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K ⟶ familyIdealTwist ι g Z r)
    (hψ : Epi ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd (toSpec A ι) g)).homEquiv _ _ ψ)) :
    Epi ψ := by
  have := hZ.epi_counit_familyIdealTwist ι n e r hr
  have : PreservesColimitsOfSize.{0, 0}
      (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd (toSpec A ι) g)).leftAdjoint_preservesColimits
  have h := (Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.snd (toSpec A ι) g)).homEquiv_counit _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.snd (toSpec A ι) g)).homEquiv _ _ ψ)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  infer_instance

include e in
/-- **The ideal of a Hilbert family is the image of `π^* π_* I_Z(r) ⊗ 𝒪(-r) ⟶ 𝒪`** (Nitsure,
arXiv:math/0504590v1, §5, p. 26, "Embedding Quot into Grassmannian", the map `h` twisted by
`-r`): for a point `Z` of `Hilb^Φ(T)`, `T` locally Noetherian, and a natural
`r ≥ hilbertRegularityBound n Φ`, `Z` is the image ideal of the counit
`π^* π_* I_Z(r) ⟶ I_Z(r) ⟶ 𝒪(r)`, tensored with `𝒪(-r)` and followed by the pairing
`𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`. -/
theorem IsHilbertFamily.imageIdealData_twistPairing_counit [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Scheme.Modules.Hom.imageIdealData
      ((((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd (toSpec A ι) g)).counit.app
          (familyIdealTwist ι g Z r) ≫ familyIdealTwistInclusion ι Z r) ▷
            familyTwistingSheaf ι g (-r)) ≫ (familyTwistPairingIso ι g r).hom) = Z := by
  have := hZ.isFiniteLocallyFree_pushforward_familyIdealTwist ι n e r hr
  have := hZ.epi_counit_familyIdealTwist ι n e r hr
  have hP : affineLocallyFiniteType _
      ((Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj
        ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
          (familyIdealTwist ι g Z r))) :=
    affineLocallyFiniteType_of_finitePresentation _
  have : ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g) ⋙
      Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj
        (familyIdealTwist ι g Z r)).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hP R j).1)
  exact imageIdealData_twistPairing_of_epi ι Z r _

end AlgebraicGeometry.ProjectiveSpace
