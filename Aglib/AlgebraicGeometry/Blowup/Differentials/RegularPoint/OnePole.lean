/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.OpenTransport
public import Aglib.AlgebraicGeometry.Blowup.PointCover
public import Aglib.AlgebraicGeometry.FunctionField.BirationalCharts
public import Aglib.AlgebraicGeometry.IdealSheaf.RegularPoint
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenLocus
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness.Open
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness.OpenGluing
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# The original global one-pole map at a regular closed point

The actual affine regular pair and the original off-centre open give a unique
raw map with the original exceptional-unit equation. Its sole bidual extension
retains that equation by forward evaluation. The original model supplies every
chart algebra and fraction-field action from its given map and given field.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u vK


open AlgebraicGeometry.Scheme.Blowup.PairIdeal
open AlgebraicGeometry.Scheme.FunctionField.BirationalCharts
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

section AffinePair

variable {X : Scheme.{u}} [IsIntegral X] {Λ : CommRingCat.{u}}
  (a : X ⟶ Spec Λ) (p : X) (hp : IsClosed ({p} : Set X))
  (hd : ringKrullDim (X.presheaf.stalk p) = 2) (n : ℕ) (L : LineBundle X)
  (φ : moduleExteriorPower X (relativeDifferentialSheaf a) n ⟶ L.val)

local notation "Y" => pointBlowup X p
local notation "b" => pointBlowdown X p
local notation "MY" => moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n
local notation "QY" => Subtype.val (dualLineBundle Y (pointIdealLine X p hp))
local notation "P" => Functor.obj (pullback b) L.val
local notation "TY" => tensorLineBundle Y (pullbackLineBundle b L)
  (dualLineBundle Y (pointIdealLine X p hp))
local notation "t" => CategoryTheory.Functor.map (pullback b) φ ≫
  NatTrans.app (positiveCartierTensorSection Y QY
    (cartierDualIdealSection (pointExceptionalι X p))) P ≫
      Iso.hom (tensorSheafBraiding Y QY P)

include hd in
private theorem existsUnique_pointRawMap_of_affinePair
    (V : X.affineOpens) (hpV : p ∈ V.1)
    (x y : Γ(X, V)) (hI : Ideal.span {x, y} = (X.fromSpecResidueField p).ker.ideal V)
    (hx : IsSMulRegular Γ(X, V) x)
    (hy : IsSMulRegular (Γ(X, V) ⧸ Ideal.span {x}) y)
    (hproper : (X.fromSpecResidueField p).ker.ideal V ≠ ⊤)
    (K : Type vK) [Field K] [Algebra Γ(X, V) K] [IsFractionRing Γ(X, V) K]
    [Algebra Λ K]
    (hTower : letI := (Spec.preimage (V.2.fromSpec ≫ a)).hom.toAlgebra
      IsScalarTower Λ Γ(X, V) K) :
    ∃! r : MY ⟶ (TY).val, rawFormsPullback a b n ≫ r = t := by
  let : Nonempty V.1 := ⟨⟨p, hpV⟩⟩
  let : IsDomain Γ(X, V) := IsIntegral.component_integral V.1
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  let α := Spec.preimage (V.2.fromSpec ≫ a)
  let : Algebra Λ Γ(X, V) := α.hom.toAlgebra
  let : IsScalarTower Λ Γ(X, V) K := hTower
  have ha : V.2.fromSpec ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(X, V))) := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      (Spec.map_preimage (V.2.fromSpec ≫ a)).symm
  let I := (X.fromSpecResidueField p).ker.ideal V
  have hcentre := Blowup.comap_fromSpec_eq_affineCenter (X.fromSpecResidueField p).ker V
  let B := pointBlowupDatum X p
  let W := Blowup.PointCover.awayOpen p B
  let v : W.toScheme ⟶ Y := W.ι
  let : IsIntegral Y := Blowup.PointCover.isIntegral p B hp hd
  let : Nonempty W.toScheme := Blowup.PointCover.awayOpen_nonempty p B hp hd
  let : IsOpenImmersion (v ≫ b) := by
    rw [← Blowup.PointCover.awayIso_hom_ι p B]
    infer_instance
  let βraw := rawFormsPullback a b n
  let : IsIso ((pullback v).map βraw) := rawFormsPullback_isIso_on_openLocus a b v n
  let : IsIso ((Scheme.Modules.restrictFunctor v).map βraw) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback v) βraw).mpr inferInstance
  let rAway : (Scheme.Modules.restrictFunctor v).obj MY ⟶
      (Scheme.Modules.restrictFunctor v).obj (TY).val :=
    inv ((Scheme.Modules.restrictFunctor v).map βraw) ≫ (Scheme.Modules.restrictFunctor v).map t
  have hAway : (Scheme.Modules.restrictFunctor v).map βraw ≫ rAway =
      (Scheme.Modules.restrictFunctor v).map t := by
    exact IsIso.hom_inv_id_assoc _ _
  let q := Blowup.PointCover.localMap p B V
  let rChart : (Scheme.Modules.restrictFunctor q).obj MY ⟶
      (Scheme.Modules.restrictFunctor q).obj (TY).val :=
    pairIdeal_rawOpenRestriction Λ Γ(X, V) K I x y hI hx hy hproper
      X p hp a V.2.fromSpec ha hcentre n L φ
  have hChart : (Scheme.Modules.restrictFunctor q).map βraw ≫ rChart =
      (Scheme.Modules.restrictFunctor q).map t :=
    pairIdeal_rawOpenRestriction_unit Λ Γ(X, V) K I x y hI hx hy hproper
      X p hp a V.2.fromSpec ha hcentre n L φ
  let Z := Blowup.PointCover.component p B V
  let c := Blowup.PointCover.componentMap p B V
  let : ∀ i, Nonempty (Z i) := Blowup.PointCover.component_nonempty p B hp V hpV hd
  let r : ∀ i, (Scheme.Modules.restrictFunctor (c i)).obj MY ⟶
      (Scheme.Modules.restrictFunctor (c i)).obj (TY).val := by
    intro i
    cases i
    · exact rAway
    · exact rChart
  have hr : ∀ i, (Scheme.Modules.restrictFunctor (c i)).map βraw ≫ r i =
      (Scheme.Modules.restrictFunctor (c i)).map t := by
    intro i
    cases i
    · exact hAway
    · exact hChart
  obtain ⟨g, hg, _⟩ := existsUnique_restrictionHom_of_openUnitSquares v βraw TY t Z c
    (Blowup.PointCover.covers p B hp V hpV) r hr
  have hunit : βraw ≫ g = t := by
    apply hom_ext_of_nonempty_restrict v (TY).property
    exact ((Scheme.Modules.restrictFunctor v).map_comp βraw g).trans
      ((congrArg (fun z => (Scheme.Modules.restrictFunctor v).map βraw ≫ z)
        (hg false)).trans hAway)
  refine ⟨g, hunit, ?_⟩
  intro g' hg'
  apply hom_ext_of_nonempty_pullback v (TY).property
  apply (cancel_epi ((pullback v).map βraw)).mp
  exact ((pullback v).map_comp βraw g').symm.trans
    ((congrArg (fun z => (pullback v).map z) (hg'.trans hunit.symm)).trans
      ((pullback v).map_comp βraw g))

end AffinePair

section OriginalModel

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {Λ A : CommRingCat.{u}} [IsDomain A]
  (ρ : Λ ⟶ A) (β : X ⟶ Spec A) [IsDominant β]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (p : X) (hp : IsClosed ({p} : Set X))
  [IsRegularLocalRing (X.presheaf.stalk p)]
  (hd : ringKrullDim (X.presheaf.stalk p) = 2)
  (n : ℕ) (L : LineBundle X)
  (φ : moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n ⟶ L.val)

local notation "a" => β ≫ Spec.map ρ
local notation "Y" => pointBlowup X p
local notation "b" => pointBlowdown X p
local notation "MY" => moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n
local notation "QY" => Subtype.val (dualLineBundle Y (pointIdealLine X p hp))
local notation "P" => Functor.obj (pullback b) L.val
local notation "TY" => tensorLineBundle Y (pullbackLineBundle b L)
  (dualLineBundle Y (pointIdealLine X p hp))
local notation "t" => CategoryTheory.Functor.map (pullback b) φ ≫
  NatTrans.app (positiveCartierTensorSection Y QY
    (cartierDualIdealSection (pointExceptionalι X p))) P ≫
      Iso.hom (tensorSheafBraiding Y QY P)

include K hβ hd in
/-- The original model and supplied field give a unique raw map with its original unit equation. -/
theorem modelPoint_existsUnique_onePoleRawMap :
    ∃! r : MY ⟶ (TY).val, rawFormsPullback a b n ≫ r = t := by
  obtain ⟨V, hpV, _, x, y, hI, hproper, hx, hy⟩ :=
    exists_regularPair_affineOpen p hd ⊤ (by trivial)
  let : Nonempty V.1 := ⟨⟨p, hpV⟩⟩
  let γ := chartFractionMap A K β hβ V.1
  let : Algebra Γ(X, V) K := γ.toAlgebra
  let : IsFractionRing Γ(X, V) K :=
    chartFractionMap_isFractionRing A K β hβ V.1 V.2
  let : Algebra Λ K := ((algebraMap A K).comp ρ.hom).toAlgebra
  let α := Spec.preimage (V.2.fromSpec ≫ a)
  let : Algebra Λ Γ(X, V) := α.hom.toAlgebra
  have hTower : IsScalarTower Λ Γ(X, V) K :=
    IsScalarTower.of_algebraMap_eq fun z =>
      (RingHom.congr_fun
        (chartFractionMap_coefficientBase A K β hβ ρ V.1 V.2) z).symm
  have hproperI : (X.fromSpecResidueField p).ker.ideal V ≠ ⊤ := by
    rwa [← hI]
  exact existsUnique_pointRawMap_of_affinePair a p hp hd n L φ V hpV x y hI hx hy
    hproperI K hTower

/-- The same unique raw map, selected without any additional compatibility hypothesis. -/
def modelPoint_onePoleRawMap : MY ⟶ (TY).val :=
  (modelPoint_existsUnique_onePoleRawMap ρ β K hβ p hp hd n L φ).exists.choose

/-- The selected raw map has the proved original exceptional-unit equation. -/
theorem modelPoint_onePoleRawMap_unit :
    rawFormsPullback a b n ≫ modelPoint_onePoleRawMap ρ β K hβ p hp hd n L φ = t :=
  (modelPoint_existsUnique_onePoleRawMap ρ β K hβ p hp hd n L φ).exists.choose_spec

/-- Extend this raw map once to the actual bidual and the actual tensor line. -/
def modelPoint_onePoleMap : dualSheaf Y (dualSheaf Y MY) ⟶ (TY).val :=
  extendToBidualLine Y TY (modelPoint_onePoleRawMap ρ β K hβ p hp hd n L φ)

/-- Original forward evaluation recovers the same raw map. -/
theorem modelPoint_onePoleMap_evaluation :
    bidualMap Y MY ≫ modelPoint_onePoleMap ρ β K hβ p hp hd n L φ =
      modelPoint_onePoleRawMap ρ β K hβ p hp hd n L φ :=
  extendToBidualLine_evaluation Y TY (modelPoint_onePoleRawMap ρ β K hβ p hp hd n L φ)

/-- The single original bidual extension retains the original global unit equation. -/
theorem modelPoint_onePoleMap_unit :
    rawFormsPullback a b n ≫ bidualMap Y MY ≫
      modelPoint_onePoleMap ρ β K hβ p hp hd n L φ = t :=
  (congrArg (fun z => rawFormsPullback a b n ≫ z)
    (modelPoint_onePoleMap_evaluation ρ β K hβ p hp hd n L φ)).trans
      (modelPoint_onePoleRawMap_unit ρ β K hβ p hp hd n L φ)

end OriginalModel

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
