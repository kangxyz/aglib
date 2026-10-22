/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Localization
public import Aglib.RingTheory.NeronModification.EvaluatedFittingBaseChange

/-! # Evaluated Fitting transport through the actual modification localization

The denominators on the modified source are the images of the original
coefficient denominators. No new centre, domain replacement, or finite-type
assertion about the localization is introduced.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

variable {R B B' ι : Type*} [CommRing R] [CommRing B] [CommRing B']
  [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
  (p : B) (g : ι → B)

local notation "M" => Modification p g
local notation "N" => Modification (algebraMap B B' p) (fun i => algebraMap B B' (g i))

omit [Algebra R B'] [IsScalarTower R B B'] in
/-- The exact comparison remains a localization at the coefficient denominators,
after simplifying the two successive images of the same submonoid. -/
theorem isLocalization_baseChangeOriginal_over_coefficients
    (Q : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid B Q) B'] :
    letI : Algebra M N :=
      @RingHom.toAlgebra M N inferInstance inferInstance
        (baseChangeOriginal (B' := B') p g).toRingHom
    IsLocalization (R := M) (Algebra.algebraMapSubmonoid M Q) N := by
  let : Algebra M N :=
    @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
  have h := isLocalization_baseChangeOriginal (B' := B') p g
    (Algebra.algebraMapSubmonoid B Q)
  simpa only [Algebra.algebraMapSubmonoid_map_map] using h

/-- Localizing the actual source modification at fixed coefficients preserves
the evaluated ideal along the actual target square. -/
theorem map_fittingIdeal_baseChangeOriginal_of_isLocalization
    (Q : Submonoid B) [IsLocalization Q B'] :
    letI : Module M (KaehlerDifferential R M) :=
      (fun (A : Type _) (hA : CommRing A) =>
        letI : CommRing A := hA
        fun (hRA : Algebra R A) =>
          letI : Algebra R A := hRA
          (inferInstance : Module A (KaehlerDifferential R A)))
        M inferInstance inferInstance
    letI : Module N (KaehlerDifferential R N) :=
      (fun (A : Type _) (hA : CommRing A) =>
        letI : CommRing A := hA
        fun (hRA : Algebra R A) =>
          letI : Algebra R A := hRA
          (inferInstance : Module A (KaehlerDifferential R A)))
        N inferInstance inferInstance
    ∀ [Module.Finite M (KaehlerDifferential R M)]
      {S S' : Type*} [CommRing S] [CommRing S']
      (χ : B →+* S) (χ' : B' →+* S') (σ : S →+* S')
      (_hpoint : χ'.comp (algebraMap B B') = σ.comp χ)
      (χM : M →+* S) (χN : N →+* S')
      (_hχM : χM.comp (of p g) = χ)
      (_hχN : χN.comp (of (algebraMap B B' p) (fun i => algebraMap B B' (g i))) = χ')
      (_hp : IsRegular (σ (χ p))) (k : ℕ),
      (Module.fittingIdeal N (KaehlerDifferential R N) k).map χN =
        ((Module.fittingIdeal M (KaehlerDifferential R M) k).map χM).map σ := by
  let : Module M (KaehlerDifferential R M) :=
    (fun (A : Type _) (hA : CommRing A) =>
      letI : CommRing A := hA
      fun (hRA : Algebra R A) =>
        letI : Algebra R A := hRA
        (inferInstance : Module A (KaehlerDifferential R A)))
      M inferInstance inferInstance
  let : Module N (KaehlerDifferential R N) :=
    (fun (A : Type _) (hA : CommRing A) =>
      letI : CommRing A := hA
      fun (hRA : Algebra R A) =>
        letI : Algebra R A := hRA
        (inferInstance : Module A (KaehlerDifferential R A)))
      N inferInstance inferInstance
  intro _ S S' _ _ χ χ' σ hpoint χM χN hχM hχN hp k
  have hsquare :
      χN.comp (baseChangeOriginal (B' := B') p g).toRingHom = σ.comp χM :=
    baseChangeOriginal_point_square (B := B) (B' := B') (S := S) (S' := S')
      p g χ χ' σ hpoint χM χN hχM hχN hp
  let : Algebra M N :=
    @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
  let : IsScalarTower R M N :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := M) (A := N) fun r =>
      (((baseChangeOriginal (B' := B') p g).restrictScalars R).commutes r).symm
  let : IsLocalization (R := M) (Algebra.algebraMapSubmonoid M Q) N :=
    isLocalization_baseChangeOriginal (B' := B') p g Q
  let F : Ideal M := Module.fittingIdeal M (KaehlerDifferential R M) k
  let F' : Ideal N := Module.fittingIdeal N (KaehlerDifferential R N) k
  have hfitting : F' = F.map (algebraMap M N) :=
    KaehlerDifferential.fittingIdeal_of_isLocalization R M N
      (Algebra.algebraMapSubmonoid M Q) k
  change F'.map χN = (F.map χM).map σ
  calc
    F'.map χN = (F.map (algebraMap M N)).map χN := congrArg (Ideal.map χN) hfitting
    _ = (F.map χM).map σ := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1

/-- The parameter localization changes both the coefficient ring and the
source modification. Its evaluated Fitting ideal is still the extension of
the original projected Fitting ideal at the SAME index and for the SAME `g`.
Here `R` is the polynomial parameter ring in the application. -/
theorem map_fittingIdeal_baseChangeOriginal_of_isLocalizationSquare
    {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' B']
    [IsScalarTower R R' B']
    (Q : Submonoid R) [IsLocalization Q R']
    [IsLocalization (Algebra.algebraMapSubmonoid B Q) B'] :
    letI : Module M (KaehlerDifferential R M) :=
      (fun (A : Type _) (hA : CommRing A) =>
        letI : CommRing A := hA
        fun (hRA : Algebra R A) =>
          letI : Algebra R A := hRA
          (inferInstance : Module A (KaehlerDifferential R A)))
        M inferInstance inferInstance
    letI : Module N (KaehlerDifferential R' N) :=
      (fun (A : Type _) (hA : CommRing A) =>
        letI : CommRing A := hA
        fun (hRA : Algebra R' A) =>
          letI : Algebra R' A := hRA
          (inferInstance : Module A (KaehlerDifferential R' A)))
        N inferInstance inferInstance
    ∀ [Module.Finite M (KaehlerDifferential R M)]
      {S S' : Type*} [CommRing S] [CommRing S']
      (χ : B →+* S) (χ' : B' →+* S') (σ : S →+* S')
      (_hpoint : χ'.comp (algebraMap B B') = σ.comp χ)
      (χM : M →+* S) (χN : N →+* S')
      (_hχM : χM.comp (of p g) = χ)
      (_hχN : χN.comp (of (algebraMap B B' p) (fun i => algebraMap B B' (g i))) = χ')
      (_hp : IsRegular (σ (χ p))) (k : ℕ),
      (Module.fittingIdeal N (KaehlerDifferential R' N) k).map χN =
        ((Module.fittingIdeal M (KaehlerDifferential R M) k).map χM).map σ := by
  let : Module M (KaehlerDifferential R M) :=
    (fun (A : Type _) (hA : CommRing A) =>
      letI : CommRing A := hA
      fun (hRA : Algebra R A) =>
        letI : Algebra R A := hRA
        (inferInstance : Module A (KaehlerDifferential R A)))
      M inferInstance inferInstance
  let : Module N (KaehlerDifferential R' N) :=
    (fun (A : Type _) (hA : CommRing A) =>
      letI : CommRing A := hA
      fun (hRA : Algebra R' A) =>
        letI : Algebra R' A := hRA
        (inferInstance : Module A (KaehlerDifferential R' A)))
      N inferInstance inferInstance
  intro _ S S' _ _ χ χ' σ hpoint χM χN hχM hχN hp k
  have hsquare :
      χN.comp (baseChangeOriginal (B' := B') p g).toRingHom = σ.comp χM :=
    baseChangeOriginal_point_square (B := B) (B' := B') (S := S) (S' := S')
      p g χ χ' σ hpoint χM χN hχM hχN hp
  let : Algebra M N :=
    @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
  let : IsScalarTower R M N :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := M) (A := N) fun r =>
      (((baseChangeOriginal (B' := B') p g).restrictScalars R).commutes r).symm
  let : IsLocalization (R := M) (Algebra.algebraMapSubmonoid M Q) N :=
    isLocalization_baseChangeOriginal_over_coefficients (R := R) p g Q
  let : Algebra.IsPushout R R' M N :=
    (Algebra.isPushout_of_isLocalization Q R' M N).symm
  let F : Ideal M := Module.fittingIdeal M (KaehlerDifferential R M) k
  let F' : Ideal N := Module.fittingIdeal N (KaehlerDifferential R' N) k
  have hfitting : F' = F.map (algebraMap M N) :=
    KaehlerDifferential.fittingIdeal_of_isPushout R R' M N k
  change F'.map χN = (F.map χM).map σ
  calc
    F'.map χN = (F.map (algebraMap M N)).map χN := congrArg (Ideal.map χN) hfitting
    _ = (F.map χM).map σ := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1

end Algebra.NeronModification
