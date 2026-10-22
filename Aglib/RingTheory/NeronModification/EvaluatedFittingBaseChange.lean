/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.BaseChange
public import Aglib.RingTheory.Kaehler.EvaluatedFittingBaseChange

/-! # Evaluated Fitting transport for the same Néron modification

The centre generators are transported literally. The comparison algebra is
induced by `baseChangeOriginal`; its pushout property comes from the existing
`baseChangeAlgEquiv`. Agreement of modification points is proved from their
restrictions and target regularity, rather than postulated as an ideal equality.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.NeronModification

section PointSquare

variable {B B' S S' ι : Type*} [CommRing B] [CommRing B'] [CommRing S] [CommRing S']
  [Algebra B B']
  (p : B) (g : ι → B)

/-- The two actual target maps on the same modification commute whenever their
original coefficient square commutes and the distinguished target element is regular. -/
theorem baseChangeOriginal_point_square
    (χ : B →+* S) (χ' : B' →+* S') (σ : S →+* S')
    (hpoint : χ'.comp (algebraMap B B') = σ.comp χ)
    (χM : Modification p g →+* S)
    (χN : Modification (algebraMap B B' p) (fun i => algebraMap B B' (g i)) →+* S')
    (hχM : χM.comp (of p g) = χ)
    (hχN : χN.comp (of (algebraMap B B' p) (fun i => algebraMap B B' (g i))) = χ')
    (hp : IsRegular (σ (χ p))) :
    χN.comp (baseChangeOriginal (B' := B') p g).toRingHom = σ.comp χM := by
  let : Algebra B S' := (σ.comp χ).toAlgebra
  let φ : Modification p g →ₐ[B] S' :=
    { χN.comp (baseChangeOriginal (B' := B') p g).toRingHom with
      commutes' := fun b => by
        change χN (baseChangeOriginal p g (of p g b)) = σ (χ b)
        rw [baseChangeOriginal_of]
        exact (RingHom.congr_fun hχN (algebraMap B B' b)).trans
          (RingHom.congr_fun hpoint b) }
  let ψ : Modification p g →ₐ[B] S' :=
    { σ.comp χM with
      commutes' := fun b => by
        change σ (χM (of p g b)) = σ (χ b)
        exact congrArg σ (RingHom.congr_fun hχM b) }
  have he : φ = ψ := algHom_ext_of_isRegular p g hp φ ψ
  exact congrArg (fun f : Modification p g →ₐ[B] S' => f.toRingHom) he

end PointSquare

section Pushout

variable {B B' ι : Type*} [CommRing B] [CommRing B'] [Algebra B B']
  (p : B) (g : ι → B)

local notation "M" => Modification p g
local notation "N" => Modification (algebraMap B B' p) (fun i => algebraMap B B' (g i))

/-- The existing flat-base-change equivalence is a pushout for the actual
comparison action, not merely an abstract equivalence of replacement rings. -/
theorem isPushout_baseChangeOriginal [Module.Flat B B'] :
    letI : Algebra M N :=
      @RingHom.toAlgebra M N inferInstance inferInstance
        (baseChangeOriginal (B' := B') p g).toRingHom
    letI : IsScalarTower B M N :=
      IsScalarTower.of_algebraMap_eq (R := B) (S := M) (A := N)
        fun b => ((baseChangeOriginal (B' := B') p g).commutes b).symm
    Algebra.IsPushout B B' M N := by
  let : Algebra M N :=
    @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
  let : IsScalarTower B M N :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := M) (A := N)
      fun b => ((baseChangeOriginal (B' := B') p g).commutes b).symm
  refine ⟨IsBaseChange.of_equiv (baseChangeAlgEquiv (B' := B') p g).toLinearEquiv ?_⟩
  intro m
  change baseChangeForward p g ((1 : B') ⊗ₜ[B] m) = baseChangeOriginal p g m
  rw [baseChangeForward_tmul, map_one, one_mul]

variable {R R' : Type*} [CommRing R] [CommRing R']
  [Algebra R R'] [Algebra R B] [Algebra R B'] [Algebra R' B']
  [IsScalarTower R B B'] [IsScalarTower R R' B']

/-- Pasting the actual source pushout with the actual modification pushout
identifies base change over the original coefficient ring. -/
theorem isPushout_baseChangeOriginal_over_coefficients
    [Algebra.IsPushout R R' B B'] [Module.Flat B B'] :
    letI : Algebra M N :=
      @RingHom.toAlgebra M N inferInstance inferInstance
        (baseChangeOriginal (B' := B') p g).toRingHom
    letI : IsScalarTower R M N :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := M) (A := N) fun r =>
        (((baseChangeOriginal (B' := B') p g).restrictScalars R).commutes r).symm
    Algebra.IsPushout R R' M N := by
  let : Algebra M N :=
    @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
  let : IsScalarTower B M N :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := M) (A := N)
      fun b => ((baseChangeOriginal (B' := B') p g).commutes b).symm
  let : IsScalarTower R M N :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := M) (A := N) fun r =>
      (((baseChangeOriginal (B' := B') p g).restrictScalars R).commutes r).symm
  let : Algebra.IsPushout R B R' B' :=
    (inferInstance : Algebra.IsPushout R R' B B').symm
  apply Algebra.IsPushout.symm
  apply (Algebra.IsPushout.comp_iff R B R' (S' := B') (T := M) (T' := N)).mpr
  exact (isPushout_baseChangeOriginal (B' := B') p g).symm

/-- The new evaluated differential Fitting ideal is the extension of the
original evaluated ideal for the SAME original centre generators. -/
theorem map_fittingIdeal_baseChangeOriginal
    [Algebra.IsPushout R R' B B'] [Module.Flat B B'] :
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
  let : Algebra.IsPushout R R' M N :=
    isPushout_baseChangeOriginal_over_coefficients (R := R) (R' := R') p g
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

end Pushout

end Algebra.NeronModification
