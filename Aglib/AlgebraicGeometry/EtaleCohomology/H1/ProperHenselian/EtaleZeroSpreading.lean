/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.ProperHenselian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodRationalResidue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartLimitZero

/-! # Proper finite-locally-constant H1 spreads zero from a rational fibre

Original H1 on the actual henselian neighborhood limit is detected by its
literal closed fibre. The residue identification and original cohomological
continuity then give one actual pointed etale neighborhood on which the
original class vanishes. No finite presentation, Noetherianity, excellence,
finite cohomology, or supplied H1-injectivity hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ProperHenselian

universe u
attribute [local instance] hasSheafifyLarge hasExtStandard
open Finite.GeometricNeighborhood Stalk

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]
  (hpoint : Function.Surjective (algebraMap R k))
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsProper p]
  (F : AbelianSheaf.{u, u + 1} Y) (hF : IsFiniteLocallyConstant F)

include hpoint hF

/-- A zero original rational-fibre class is zero on the actual henselian
neighborhood limit, by the proved proper-henselian H1 theorem. -/
theorem h1Pullback_limit_eq_zero
    (δ : Sheaf.H.{u + 2} F 1)
    (hδ : h1Pullback (pullback.snd (Spec.algebraMap R k) p) F δ = 0) :
    h1Pullback (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R k)) p) F δ = 0 := by
  let H := GeometricEtaleColimit R k
  let c := Spec.algebraMap R H
  let pH := pullback.fst c p
  let fH := pullback.snd c p
  let r := LocalRing.residueSpecMap H
  let iH := pullback.fst pH r
  let e := rationalResidueFiberIso R k hpoint p
  let FH := (inverseImage fH).obj F
  have htriangle : e.hom ≫ pullback.snd (Spec.algebraMap R k) p = iH ≫ fH :=
    rationalResidueFiberIso_hom_snd R k hpoint p
  have htotal : cohomologyPullback (iH ≫ fH) F 1 δ = 0 := by
    have ht := cohomologyTransfer_pullbackTriangle (iH ≫ fH)
      (pullback.snd (Spec.algebraMap R k) p) e.hom htriangle F 1 δ
    rw [cohomologyPullback_one, hδ, map_zero] at ht
    exact ht.symm
  have hclosed : h1Pullback iH FH (h1Pullback fH F δ) = 0 := by
    have hc := cohomologyPullback_comp fH iH F 1 δ
    rw [htotal, map_zero] at hc
    exact hc.symm
  have hFH : IsFiniteLocallyConstant FH := isFiniteLocallyConstant_pullback fH hF
  have hinj := (ConstantFinite.properHenselian_h1Pullback_bijective pH FH hFH).injective
  exact hinj (hclosed.trans (map_zero _).symm)

/-- Proper finite-locally-constant original H1 vanishing at a rational fibre
vanishes on one actual pointed etale neighborhood of the original affine base. -/
theorem exists_etale_h1Pullback_eq_zero
    (δ : Sheaf.H.{u + 2} F 1)
    (hδ : h1Pullback (pullback.snd (Spec.algebraMap R k) p) F δ = 0) :
    ∃ U : GeometricEtaleNeighborhood R k,
      h1Pullback (pullback.snd (Spec.algebraMap R U.algebra) p) F δ = 0 := by
  have hlimit := h1Pullback_limit_eq_zero R k hpoint p F hF δ hδ
  have hlimit' : cohomologyPullback
      (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R k) ≫ 𝟙 _) p) F 1 δ = 0 := by
    let P : (Spec (.of (GeometricEtaleColimit R k)) ⟶ Spec (.of R)) → Prop :=
      fun g => cohomologyPullback (pullback.snd g p) F 1 δ = 0
    exact (congrArg P
      (Category.comp_id (Spec.algebraMap R (GeometricEtaleColimit R k)))).mpr hlimit
  obtain ⟨U, hU⟩ := exists_chart_cohomologyPullback_eq_zero R k (𝟙 _) p F 1 δ hlimit'
  refine ⟨U, ?_⟩
  let P : (Spec (.of U.algebra) ⟶ Spec (.of R)) → Prop :=
    fun g => cohomologyPullback (pullback.snd g p) F 1 δ = 0
  exact (congrArg P (Category.comp_id (Spec.algebraMap R U.algebra))).mp hU

end AlgebraicGeometry.Scheme.EtaleCohomology.ProperHenselian
