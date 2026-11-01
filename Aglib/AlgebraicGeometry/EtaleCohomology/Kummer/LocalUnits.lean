/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootAddition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClassification
public import Aglib.AlgebraicGeometry.Picard.LocalKummer
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Original positive root classes of local-ring units modulo powers

The actual positive root-class homomorphism descends to the native quotient
of actual units by nth powers. Its kernel is supplied by the proved torsor
classification. For local spectra the existing actual line-bundle triviality
makes this map surjective. The quotient equivalence retains the original
class and sign; no global-unit root-surjectivity hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients

namespace GroupCohomology.Kummer.Torsor

universe u w

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The original positive root-class homomorphism has exactly the nth-power kernel. -/
theorem rootClassHom_ker :
    (rootClassHom RootCover.etalePowerSurjectivity X n hn hinv).ker =
      (nsmulAddMonoidHom (α := Additive Γ(X, ⊤)ˣ) n).range := by
  ext a
  change rootClass RootCover.etalePowerSurjectivity X n hn hinv a.toMul = 0 ↔
    ∃ b : Additive Γ(X, ⊤)ˣ, n • b = a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (rootClass_eq_zero_iff RootCover.etalePowerSurjectivity
      X n hn hinv (stacks03AJ X) a.toMul).mp ha
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  · rintro ⟨b, rfl⟩
    exact rootClass_eq_zero_of_power RootCover.etalePowerSurjectivity X n hn hinv b.toMul

/-- The actual positive root-class map on the native quotient of global units. -/
def unitQuotientRootClass :
    Additive Γ(X, ⊤)ˣ ⧸ (nsmulAddMonoidHom (α := Additive Γ(X, ⊤)ˣ) n).range →+
      H1Etale X (mu X n) :=
  QuotientAddGroup.lift _ (rootClassHom RootCover.etalePowerSurjectivity X n hn hinv)
    (rootClassHom_ker X n hn hinv).symm.le

/-- Its representative is the original positive root torsor class. -/
@[simp] theorem unitQuotientRootClass_mk (a : Additive Γ(X, ⊤)ˣ) :
    unitQuotientRootClass X n hn hinv (QuotientAddGroup.mk a) =
      rootClass RootCover.etalePowerSurjectivity X n hn hinv a.toMul := rfl

/-- Units modulo powers inject into original H1 on any scheme. -/
theorem unitQuotientRootClass_injective :
    Function.Injective (unitQuotientRootClass X n hn hinv) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).mpr
    (rootClassHom_ker X n hn hinv).symm

end GroupCohomology.Kummer.Torsor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open GroupCohomology.Kummer.Torsor

universe u w

variable (R : CommRingCat.{u}) [IsLocalRing R]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec R, ⊤)))

/-- Actual global units modulo powers classify original root H1 on a local
spectrum, with the original positive forward map. -/
def localGlobalUnitQuotientRootEquiv :
    Additive Γ(Spec R, ⊤)ˣ ⧸
        (nsmulAddMonoidHom (α := Additive Γ(Spec R, ⊤)ˣ) n).range ≃+
      H1Etale (Spec R) (mu (Spec R) n) :=
  AddEquiv.ofBijective (unitQuotientRootClass (Spec R) n hn hinv)
    ⟨unitQuotientRootClass_injective (Spec R) n hn hinv, by
      intro c
      obtain ⟨a, ha⟩ := LocalKummer.localRootClass_surjective R
        EtaleDescent.etaleLineBundleDescent (stacks03AJ (Spec R)) n hn hinv c
      exact ⟨QuotientAddGroup.mk (Additive.ofMul a), ha⟩⟩

/-- The actual affine scalar identification on units, oriented from ring
units to the original global-section units. -/
def ringGlobalUnitsEquiv : Additive Rˣ ≃+ Additive Γ(Spec R, ⊤)ˣ :=
  (Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.toMulEquiv).toAdditive

/-- Native quotient transport along the original Gamma-Spec unit equivalence. -/
def ringGlobalUnitsQuotientEquiv :
    Additive Rˣ ⧸ (nsmulAddMonoidHom (α := Additive Rˣ) n).range ≃+
      Additive Γ(Spec R, ⊤)ˣ ⧸
        (nsmulAddMonoidHom (α := Additive Γ(Spec R, ⊤)ˣ) n).range :=
  QuotientAddGroup.congr _ _ (ringGlobalUnitsEquiv R) (by
    ext a
    constructor
    · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
      exact ⟨ringGlobalUnitsEquiv R c, (map_nsmul (ringGlobalUnitsEquiv R).toAddMonoidHom n c).symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨n • (ringGlobalUnitsEquiv R).symm b, ⟨_, rfl⟩, ?_⟩
      exact (map_nsmul (ringGlobalUnitsEquiv R).toAddMonoidHom
        n ((ringGlobalUnitsEquiv R).symm b)).trans
          (congrArg (fun a => n • a) ((ringGlobalUnitsEquiv R).apply_symm_apply b)))

/-- Actual local-ring units modulo nth powers identify with original H1 of
roots of unity. In particular this applies to every field, with no choice
of a separable closure or independent cohomology model. -/
def localUnitQuotientRootEquiv :
    Additive Rˣ ⧸ (nsmulAddMonoidHom (α := Additive Rˣ) n).range ≃+
      H1Etale (Spec R) (mu (Spec R) n) :=
  (ringGlobalUnitsQuotientEquiv R n).trans
    (localGlobalUnitQuotientRootEquiv R n hn hinv)

/-- The quotient equivalence retains exactly the original positive root class
of the ring unit transported by the original Gamma-Spec inverse. -/
theorem localUnitQuotientRootEquiv_mk (a : Additive Rˣ) :
    localUnitQuotientRootEquiv R n hn hinv (QuotientAddGroup.mk a) =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec R) n hn hinv ((ringGlobalUnitsEquiv R a).toMul) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
