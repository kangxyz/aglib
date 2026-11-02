/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LocalUnits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Pullback

/-! # The original positive unit image in Kummer H1

The original coefficient inclusion followed by the inverse actual Picard
comparison has kernel exactly the original positive root-class image. Actual
power-pair descent and trivialization prove this without identifying a
connecting morphism by a guessed sign, choosing roots of global units, or
putting another group structure on power-pair classes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.Torsor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original Kummer inclusion, expressed in the actual Picard group. -/
def kummerPicardMap (n : ℕ) : H1Etale X (mu X n) →+ PicardGroup X :=
  (picardCohomologyEquiv X).symm.toAddMonoidHom.comp
    (coefficientMap.{u, u + 1, w} (X := X) (inclusion X n))

variable (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Every original Kummer H1 class has an actual descended power-pair representative.
The genuine torsor and line-bundle descent suppliers are applied internally. -/
theorem exists_powerPair_h1Representative (c : H1Etale X (mu X n)) :
    ∃ P : TrivializedPower.Pair X n,
      torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
        X n hn hinv P) = c := by
  obtain ⟨d, hd⟩ := ((stacks03AJ X).bijective (mu X n)).surjective c
  obtain ⟨P, rfl⟩ := Quotient.exists_rep d
  refine ⟨PowerDescent.pair P EtaleDescent.etaleLineBundleDescent, ?_⟩
  exact (torsorExtClass_iso (PowerDescent.torsorRecovery P
    EtaleDescent.etaleLineBundleDescent hn hinv)).symm.trans hd

/-- The original Picard image of a power-frame class is its underlying line bundle. -/
theorem kummerPicardMap_powerPair (P : TrivializedPower.Pair X n) :
    kummerPicardMap X n
      (torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
        X n hn hinv P)) = classOf X P.lineBundle := by
  exact (congrArg (picardCohomologyEquiv X).symm
    (torsorExtClass_naturality (KummerH1.forgetCompatible
      EtaleDescent.etaleLineBundleDescent X n hn hinv P))).trans
        ((picardCohomologyEquiv X).symm_apply_apply (classOf X P.lineBundle))

/-- The original positive unit-root class has trivial original Picard image. -/
theorem kummerPicardMap_rootClass (a : Γ(X, ⊤)ˣ) :
    kummerPicardMap X n
      (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv a) =
      0 := by
  exact (congrArg (kummerPicardMap X n)
    (PowerRoot.torsorExtClass_unitPair EtaleDescent.etaleLineBundleDescent
      X n hn hinv a)).symm.trans
        ((kummerPicardMap_powerPair X n hn hinv (PowerRoot.unitPair X n a)).trans
          (Quotient.sound ⟨(CategoryTheory.Limits.coproductUniqueIso
            (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩))

include hn hinv in
/-- Every original Picard image is annihilated by the actual level. -/
theorem nsmul_kummerPicardMap (c : H1Etale X (mu X n)) :
    n • kummerPicardMap X n c = 0 := by
  obtain ⟨P, rfl⟩ := exists_powerPair_h1Representative X n hn hinv c
  rw [kummerPicardMap_powerPair]
  exact (classOf_tensorPower X P.lineBundle n).symm.trans
    (Quotient.sound ⟨P.trivialization ≪≫ (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩)

/-- The exact original positive unit image is the kernel of the original Picard map. -/
theorem rootClassHom_range_eq_kummerPicardMap_ker :
    (rootClassHom GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
      X n hn hinv).range = (kummerPicardMap X n).ker := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact kummerPicardMap_rootClass X n hn hinv a.toMul
  · intro hc
    obtain ⟨P, hP⟩ := exists_powerPair_h1Representative X n hn hinv c
    have hL : classOf X P.lineBundle = 0 :=
      (kummerPicardMap_powerPair X n hn hinv P).symm.trans
        ((congrArg (kummerPicardMap X n) hP).trans hc)
    obtain ⟨e⟩ := Quotient.exact
      (show classOf X P.lineBundle = classOf X (trivialLineBundle X) from hL)
    let e' := e ≪≫ CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
    obtain ⟨a, ha⟩ := LocalKummer.pair_isomorphic_unitPair_of_trivial X n P e'
    have hpair := torsorExtClass_iso (KummerH1.pairTorsorIso
      EtaleDescent.etaleLineBundleDescent X n hn hinv
      (P := P) (Q := PowerRoot.unitPair X n a) e' ha)
    have hroot := PowerRoot.torsorExtClass_unitPair
      EtaleDescent.etaleLineBundleDescent X n hn hinv a
    exact ⟨Additive.ofMul a, (hpair.trans hroot).symm.trans hP⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
