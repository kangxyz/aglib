/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Original Dedekind height-one localizations and their actual scheme stalks -/

@[expose] public noncomputable section
namespace AlgebraicGeometry.DedekindPointStalk

open IsDedekindDomain
variable {S : Type*} [CommRing S] [IsDedekindDomain S]

/-- The literal prime point, with no choice of an abstract residue field. -/
abbrev point (q : HeightOneSpectrum S) : PrimeSpectrum S := ⟨q.asIdeal, inferInstance⟩

local instance stalkLocalization (q : HeightOneSpectrum S) :
    IsLocalization.AtPrime ((Spec.structureSheaf S).presheaf.stalk (point q)) q.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk S (point q)

local instance stalkDomain (q : HeightOneSpectrum S) :
    IsDomain ((Spec.structureSheaf S).presheaf.stalk (point q)) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ q.asIdeal.primeCompl_le_nonZeroDivisors

local instance stalkLocal (q : HeightOneSpectrum S) :
    IsLocalRing ((Spec.structureSheaf S).presheaf.stalk (point q)) :=
  IsLocalization.AtPrime.isLocalRing _ q.asIdeal

/-- The canonical equivalence is over the original ring and its original maps. -/
def localizationEquiv (q : HeightOneSpectrum S) :
    Localization.AtPrime q.asIdeal ≃ₐ[S] ((Spec.structureSheaf S).presheaf.stalk (point q)) :=
  IsLocalization.algEquiv q.asIdeal.primeCompl _ _

/-- Nonzero original points have actual DVR stalks. -/
instance stalkDVR (q : HeightOneSpectrum S) :
    IsDiscreteValuationRing ((Spec.structureSheaf S).presheaf.stalk (point q)) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot _

/-- The residue equivalence is induced by the actual local-ring equivalence. -/
def residueEquiv (q : HeightOneSpectrum S) :
    IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal) ≃+*
      IsLocalRing.ResidueField ((Spec.structureSheaf S).presheaf.stalk (point q)) :=
  IsLocalRing.ResidueField.mapEquiv (localizationEquiv q).toRingEquiv

omit [IsDedekindDomain S] in
/-- Original scalar reduction is preserved by this specific equivalence. -/
theorem residueEquiv_algebraMap (q : HeightOneSpectrum S) (s : S) :
    residueEquiv q (IsLocalRing.residue (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) s)) =
        IsLocalRing.residue ((Spec.structureSheaf S).presheaf.stalk (point q))
          (StructureSheaf.toStalk S (point q) s) := by
  simp only [residueEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue _) ((localizationEquiv q).commutes s)

end AlgebraicGeometry.DedekindPointStalk
