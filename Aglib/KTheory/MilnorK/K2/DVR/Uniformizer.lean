/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.DVR.Basic

/-!
# Uniformizer-independent Milnor specialization for an actual DVR

Any two irreducible uniformizers of a mathlib DVR differ by an actual ring
unit. Their normalized unit residues differ by the negative valuation power
of the residue of that unit. This derives the unit-part-change relation used
in `Specialization.lean`, so its tame invariance and specialization correction
theorems apply without a supplied change relation. The correction vanishes on
the genuine Milnor tame kernel.

Source correspondence: `K2-018#sec:k2018-splitting`, lines 240–249, and
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, in
`research/exposes/K2/018/expose.tex` at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
Every declaration below provides elementary DVR background for those source
assertions. The DVR and fraction-field instances remain hypotheses; the
origin-local-ring DVR realization, Quillen comparison, cohomological residue,
and arithmetic integrality are outside this module's scope.

Implementation basis: `DVRRealization.lean` SHA256
`c6d8cb601ec3a3a3e0beee5ae790e2014aba991545db33e8a125812b33312f37`;
`Specialization.lean` and `Residue.lean` at
`ac804cb2f648f42380e612235b972786506d0b9f`; Lean `4.34.1`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Implementation provenance

Original R5 implementation:
https://github.com/kangxyz/r5-lab/blob/1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e/lean/R5Lab/KTheory/MilnorK2/DVR/Uniformizer.lean
Original Git blob SHA-1: `e67b46fca44619f52849f94eb2f671747b6a46ec`.
Original SHA-256: `2afdfc3041049ea4ef56d419e8483e122b14982fd4ca6ec1220bb12ca9c567c9`.
-/

noncomputable section

@[expose] public section

namespace MilnorK.K2.DVR

open IsLocalRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual ring unit relating two irreducible uniformizers; source snapshot above. -/
def uniformizerRatio {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π') : Rˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible R hπ hπ').choose

/-- The chosen ratio satisfies `π' = wπ` in the DVR; source snapshot above. -/
theorem uniformizerRatio_spec {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π') :
    π' = (uniformizerRatio hπ hπ' : R) * π := by
  calc
    π' = π * (uniformizerRatio hπ hπ' : R) :=
      (IsDiscreteValuationRing.associated_of_irreducible R hπ hπ').choose_spec.symm
    _ = _ := mul_comm _ _

/-- The same ratio relates the genuine fraction-field units; source snapshot above. -/
theorem uniformizer_change {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π') :
    uniformizer (K := K) hπ' =
      fieldUnits R K (uniformizerRatio hπ hπ') * uniformizer (K := K) hπ := by
  apply Units.ext
  change algebraMap R K π' =
    algebraMap R K (uniformizerRatio hπ hπ' : R) * algebraMap R K π
  exact (congrArg (algebraMap R K) (uniformizerRatio_spec hπ hπ')).trans
    (map_mul _ _ _)

/-- Normalized fraction-field units change by the negative valuation power of the ratio.
Source: elementary DVR background at the module snapshot. -/
theorem normalizedUnit_change {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π')
    (a : Kˣ) :
    normalizedUnit (K := K) hπ' a = normalizedUnit (K := K) hπ a *
      fieldUnits R K (uniformizerRatio hπ hπ') ^ (-value R K (Additive.ofMul a)) := by
  change a * uniformizer (K := K) hπ' ^ (-value R K (Additive.ofMul a)) =
    (a * uniformizer (K := K) hπ ^ (-value R K (Additive.ofMul a))) *
      fieldUnits R K (uniformizerRatio hπ hπ') ^ (-value R K (Additive.ofMul a))
  rw [uniformizer_change hπ hπ', mul_zpow]
  ac_rfl

/-- Uniqueness of embedded ring units gives the actual normalized-lift change formula.
Source: elementary DVR background at the module snapshot. -/
theorem normalizedLift_change {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π')
    (a : Kˣ) :
    normalizedLift (K := K) hπ' a = normalizedLift (K := K) hπ a *
      uniformizerRatio hπ hπ' ^ (-value R K (Additive.ofMul a)) := by
  apply fieldUnits_injective R K
  rw [normalizedLift_spec, map_mul, map_zpow, normalizedLift_spec, normalizedUnit_change]

/-- Actual unit reduction preserves the normalized-lift change formula.
Source: elementary DVR background at the module snapshot. -/
theorem unitResidue_change {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π')
    (a : Kˣ) :
    unitResidue (K := K) hπ' a = unitResidue (K := K) hπ a *
      Units.map (residue R).toMonoidHom (uniformizerRatio hπ hπ') ^
        (-value R K (Additive.ofMul a)) := by
  change Units.map (residue R).toMonoidHom (normalizedLift (K := K) hπ' a) = _
  rw [normalizedLift_change, map_mul, map_zpow]
  rfl

/-- Additive notation for the actual residue of the ratio unit; source snapshot above. -/
def uniformizerChange {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π') :
    UnitsAdd (ResidueField R) :=
  Additive.ofMul (Units.map (residue R).toMonoidHom (uniformizerRatio hπ hπ'))

/-- The concrete normalized residue maps satisfy `r' = r - v ε`.
Source: auxiliary uniformizer-change identity at the module snapshot. -/
theorem unitPart_change {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π')
    (a : UnitsAdd K) :
    (data (K := K) hπ').unitPart a = (data (K := K) hπ).unitPart a -
      (data (K := K) hπ).value a • uniformizerChange hπ hπ' := by
  change Additive.ofMul (unitResidue (K := K) hπ' a.toMul) =
    Additive.ofMul (unitResidue (K := K) hπ a.toMul) -
      value R K a • Additive.ofMul
        (Units.map (residue R).toMonoidHom (uniformizerRatio hπ hπ'))
  rw [unitResidue_change, ofMul_mul, ofMul_zpow, neg_zsmul]
  rfl

/-- The integer order in actual DVR data does not depend on the uniformizer.
Source: elementary DVR background at the module snapshot. -/
theorem data_value_eq {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π') :
    (data (K := K) hπ').value = (data (K := K) hπ).value := rfl

/-- The genuine Milnor tame homomorphism is independent of the actual uniformizer.
Source: `K2-018#lem:k2018-residue-bockstein` at the module snapshot. -/
theorem tame_uniformizer_independent {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    tame (data (K := K) hπ') = tame (data (K := K) hπ) :=
  tame_eq_of_unitPart_change (data hπ) (data hπ') (uniformizerChange hπ hπ')
    (fun _ => rfl) (unitPart_change hπ hπ')

/-- Therefore both actual uniformizers give exactly the same Milnor tame kernel.
Source: auxiliary canonicalization at the module snapshot. -/
theorem tame_kernel_uniformizer_independent {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    (tame (data (K := K) hπ')).ker = (tame (data (K := K) hπ)).ker :=
  tame_kernel_eq_of_unitPart_change (data hπ) (data hπ') (uniformizerChange hπ hπ')
    (fun _ => rfl) (unitPart_change hπ hπ')

/-- The concrete full-group specialization changes by `-{∂(-), ε}`.
Source: auxiliary specialization correction for `K2-018#sec:k2018-splitting`
at the module snapshot. -/
theorem specialize_uniformizer_change {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    specialize (data (K := K) hπ') (unitReductionCompatible hπ') =
      specialize (data (K := K) hπ) (unitReductionCompatible hπ) -
        (residueCorrection (uniformizerChange hπ hπ')).comp (tame (data (K := K) hπ)) :=
  specialize_change (data hπ) (data hπ') (unitReductionCompatible hπ)
    (unitReductionCompatible hπ') (uniformizerChange hπ hπ') (unitPart_change hπ hπ')

/-- The source convention for the concrete correction is `s'(x)-s(x)={ε,∂x}`.
Source: auxiliary specialization correction for `K2-018#sec:k2018-splitting`
at the module snapshot. -/
theorem specialize_uniformizer_change_source_convention {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') (x : Group K) :
    specialize (data (K := K) hπ') (unitReductionCompatible hπ') x -
      specialize (data (K := K) hπ) (unitReductionCompatible hπ) x =
        symbolBilinear (ResidueField R) (uniformizerChange hπ hπ') (tame (data hπ) x) :=
  specialize_change_source_convention (data hπ) (data hπ') (unitReductionCompatible hπ)
    (unitReductionCompatible hπ') (uniformizerChange hπ hπ') (unitPart_change hπ hπ') x

/-- The actual specialization maps agree on the genuine Milnor tame kernel.
Together with `tame_kernel_uniformizer_independent`, this removes all supplied
uniformizer-change premises from canonical specialization for a DVR.
Source: the field-specialization part of `K2-018#sec:k2018-splitting`
at the module snapshot; no arithmetic `B₂(F)` landing is asserted. -/
theorem unramifiedSpecialize_uniformizer_independent {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    (specialize (data (K := K) hπ') (unitReductionCompatible hπ')).comp
        (tame (data (K := K) hπ)).ker.subtype =
      unramifiedSpecialize (data (K := K) hπ) (unitReductionCompatible hπ) :=
  specialize_eq_on_tame_kernel (data hπ) (data hπ') (unitReductionCompatible hπ)
    (unitReductionCompatible hπ') (uniformizerChange hπ hπ') (unitPart_change hπ hπ')

/-- Pointwise uniformizer independence for every class in the actual tame kernel.
Source: the field-specialization part of `K2-018#sec:k2018-splitting`
at the module snapshot. -/
theorem specialize_uniformizer_independent {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') (x : Group K)
    (hx : tame (data (K := K) hπ) x = 0) :
    specialize (data (K := K) hπ') (unitReductionCompatible hπ') x =
      specialize (data (K := K) hπ) (unitReductionCompatible hπ) x := by
  have h := LinearMap.congr_fun (unramifiedSpecialize_uniformizer_independent hπ hπ')
    (⟨x, hx⟩ : (tame (data (K := K) hπ)).ker)
  exact h

end MilnorK.K2.DVR
