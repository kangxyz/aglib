/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.LineBundleEvaluation
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FibreCriterion
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.PositiveSection` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5c68d739e563260a75d38ced188cc17fce34e77f1e78e62a0643da4f64b963b0`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated adjoint_pullback_ne_zero)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle dualLineBundle isLocallyRankOne_of_iso lineBundle_isLocallyFree
    pullbackLineBundle trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# The actual positive-divisor section and its direct image

The section O → Hom(I_D,O) is literally the canonical transpose of the actual
kernel-ideal inclusion. The canonical 056Q fibre-ideal comparison proves
nonvanishing after every integral geometric-fibre pullback. The actual
pullback/pushforward adjunction then proves that the corresponding map
O_base → p_*O(D) remains nonzero on every such fibre.

A nonzero map between line bundles on Spec K is proved invertible directly:
actual unit trivializations reduce it to the scalar given by its value at 1,
and field inversion proves every component bijective. This proof imports no
C3 trivialized-power or Kummer layer. The optional broad finite-locally-free
geometric-fibre criterion finally gives the direct-image map IsIso when its
actual coherent fibre profile has rank one and its original base is locally
Noetherian. No graph recovery or Abel inverse
identity is supplied as a premise or yet asserted by this module.
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace


open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
variable {X S D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X)
variable (hI : IsLocallyRankOne X (idealModule i))
/-- The positive-divisor section, given by transposing the actual kernel-ideal
inclusion into a map from the structure sheaf to the dual ideal line bundle. -/
def divisorPositiveSection :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (show X.Modules from (dualLineBundle X ⟨idealModule i, hI⟩).val) :=
  AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X (idealInclusion i)

variable (hbase : RelativeCartierIdealBaseChange.{u})
variable [IsClosedImmersion i] [Flat (i ≫ p)]
include hbase in
theorem divisorPositiveSection_fibre_ne_zero (K : Type u) [Field K] (t : Spec (.of K) ⟶ S)
    [IsIntegral (pullback p t)] :
    (Scheme.Modules.pullback (pullback.fst p t)).map (divisorPositiveSection i hI) ≠ 0 := by
  apply transpose_pullback_ne_zero (pullback.fst p t) ⟨idealModule i, hI⟩ (idealInclusion i)
  intro hz
  have hm : Mono ((Scheme.Modules.pullback (pullback.fst p t)).map (idealInclusion i) ≫
      SheafOfModules.pullbackObjUnitToUnit (pullback.fst p t).toRingCatSheafHom) := by
    rw [← fibreIdealIso_inclusion p i t hbase hI]
    infer_instance
  have hn := lineBundleMap_ne_zero_of_mono (pullback p t)
    (pullbackLineBundle (pullback.fst p t) ⟨idealModule i, hI⟩)
    ((Scheme.Modules.pullback (pullback.fst p t)).map (idealInclusion i) ≫
      SheafOfModules.pullbackObjUnitToUnit (pullback.fst p t).toRingCatSheafHom)
  apply hn
  rw [hz, zero_comp]

/-- The adjoint of the positive-divisor section under the actual module
pullback/pushforward adjunction, using the canonical pullback of the unit. -/
def divisorPositiveAdjoint :
    (show S.Modules from SheafOfModules.unit S.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward p).obj (dualLineBundle X ⟨idealModule i, hI⟩).val :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
    ((pullbackUnitIso p).hom ≫ divisorPositiveSection i hI)

include hbase in
theorem divisorPositiveAdjoint_fibre_ne_zero (K : Type u) [Field K] (t : Spec (.of K) ⟶ S)
    [IsIntegral (pullback p t)] :
    (Scheme.Modules.pullback t).map (divisorPositiveAdjoint p i hI) ≠ 0 := by
  apply adjoint_pullback_ne_zero p t
  rw [Functor.map_comp]
  intro h
  apply divisorPositiveSection_fibre_ne_zero p i hI hbase K t
  apply (cancel_epi ((Scheme.Modules.pullback (pullback.fst p t)).map (pullbackUnitIso p).hom)).mp
  simpa using h
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible
variable (K : Type u) [Field K]
theorem fieldUnitMap_isIso_of_ne_zero
    (φ : (show (Spec (.of K)).Modules from SheafOfModules.unit (Spec (.of K)).ringCatSheaf) ⟶
      (show (Spec (.of K)).Modules from SheafOfModules.unit (Spec (.of K)).ringCatSheaf))
    (hφ : φ ≠ 0) : IsIso φ :=
  AlgebraicGeometry.Scheme.Modules.Invertible.fieldUnitMap_isIso_of_ne_zero K φ hφ

theorem fieldLineBundleMap_isIso_of_ne_zero (L M : LineBundle (Spec (.of K)))
    (φ : (show (Spec (.of K)).Modules from L.val) ⟶ (show (Spec (.of K)).Modules from M.val))
    (hφ : φ ≠ 0) : IsIso φ :=
  AlgebraicGeometry.Scheme.Modules.Invertible.fieldLineBundleMap_isIso_of_ne_zero K L M φ hφ
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
/-- The structure sheaf as a line bundle, with its canonical rank-one trivialization. -/
def structureLineBundle (X : Scheme.{u}) : LineBundle X := by
  let e : (trivialLineBundle X).val ≅ SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.ringCatSheaf)
  exact ⟨SheafOfModules.unit X.ringCatSheaf,
    isLocallyRankOne_of_iso X e (trivialLineBundle X).property⟩

variable {X S D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X)
variable (hI : IsLocallyRankOne X (idealModule i))
variable (hbase : RelativeCartierIdealBaseChange.{u})
variable [IsClosedImmersion i] [Flat (i ≫ p)]
variable [IsProper p] [LocallyOfFinitePresentation p] [Flat p]
variable [IsLocallyNoetherian S]
variable (hL : FibreCohomologyConcentrated p (dualLineBundle X ⟨idealModule i, hI⟩).val 1)
include hbase hL in
theorem divisorPositiveAdjoint_isIso (hcriterion :
    AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeGeometricIso.{u})
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      IsIntegral (pullback p t)) : IsIso (divisorPositiveAdjoint p i hI) := by
  let L := dualLineBundle X ⟨idealModule i, hI⟩
  let P := Scheme.Cohomology.directImageLineBundle p L hL
  apply hcriterion S (structureLineBundle S).val P.val (divisorPositiveAdjoint p i hI)
    (lineBundle_isLocallyFree S (structureLineBundle S))
    (lineBundle_isFinitePresentation S (structureLineBundle S))
    (lineBundle_isLocallyFree S P) (lineBundle_isFinitePresentation S P)
  intro K _ _ t
  letI := hcurves K t
  exact fieldLineBundleMap_isIso_of_ne_zero K (pullbackLineBundle t (structureLineBundle S))
    (pullbackLineBundle t P) ((Scheme.Modules.pullback t).map (divisorPositiveAdjoint p i hI))
    (divisorPositiveAdjoint_fibre_ne_zero p i hI hbase K t)
end AlgebraicGeometry.Scheme.Hom

