/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.OpenComparison
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.StrictTransformClosure
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Blowup.StructuralFlatness

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.StrictTransformCover`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`2c487b89f159bc11256bc673307f85a0d31dc8d17c6943d661a9e98c9bc2881f`.
Only generic actual-node/pointed-state middle exclusion and retained outer charts:
  source12–237,638–1077,1208–1310. Original Weierstrass component assembly remains separately
  tracked.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section MiddleSpecialContraction

/-! The whole first middle residue fibre contracts to the original node,
including when the middle exponent is zero. This is a morphism equality on
the full scheme, not a statement only about its distinguished point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {π : R} (hπ : Irreducible π) (m : ℕ)
local notation "k" => ResidueField R

lemma middleSpecialization_comp :
    (PlaneNode.coefficientMap (S := k) (π^m)).comp (middleBase π m) =
      (IsScalarTower.toAlgHom R k (PlaneNode.Ring (algebraMap R k (π^m)))).comp
        (PlaneNode.residueMap (π^(m + 2))
          (IsDiscreteValuationRing.power_residue_zero π hπ (m + 2) (by omega))) := by
  have hscalar : algebraMap R (PlaneNode.Ring (algebraMap R k (π ^ m))) π = 0 := by
    have hz : algebraMap R k π = 0 := by
      simpa only [ResidueField.algebraMap_eq] using
        IsDiscreteValuationRing.uniformizer_residue_zero π hπ
    rw [IsScalarTower.algebraMap_eq R k (PlaneNode.Ring (algebraMap R k (π ^ m)))]
    change algebraMap k (PlaneNode.Ring (algebraMap R k (π ^ m))) (algebraMap R k π) = 0
    rw [hz, map_zero]
  apply PlaneNode.hom_ext
  · simp only [AlgHom.comp_apply, middleBase, PlaneNode.lift_U, map_mul,
      PlaneNode.residueMap, map_zero]
    rw [(PlaneNode.coefficientMap k (π ^ m)).commutes π, hscalar, zero_mul]
  · simp only [AlgHom.comp_apply, middleBase, PlaneNode.lift_V, map_mul,
      PlaneNode.residueMap, map_zero]
    rw [(PlaneNode.coefficientMap k (π ^ m)).commutes π, hscalar, zero_mul]

/-- The contraction of the full literal special fibre of the first middle
node, before any choice of a point or irreducible component. -/
@[reassoc] lemma middleSpecialFibre_contracts :
    pullback.fst (base (π := π) (n := m)) residueBase ≫
      Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
        pullback.snd (base (π := π) (n := m)) residueBase ≫
          NextCenter.origin π hπ (m + 2) (by omega) := by
  let e := Scheme.PowerNode.specializationIso (S := k) (π ^ m)
  have hfst : e.hom ≫ pullback.fst (base (π := π) (n := m)) residueBase =
      Spec.map (CommRingCat.ofHom (PlaneNode.coefficientMap k (π ^ m)).toRingHom) :=
    Scheme.PowerNode.specializationIso_hom_fst (S := k) (π ^ m)
  have hsnd : e.hom ≫ pullback.snd (base (π := π) (n := m)) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k (PlaneNode.Ring
        (algebraMap R k (π ^ m))))) :=
    Scheme.PowerNode.specializationIso_hom_snd (S := k) (π ^ m)
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, hfst, ← Category.assoc, hsnd,
    NextCenter.origin, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (middleSpecialization_comp hπ m)

/-- Any scheme lying over this residue middle fibre has the same actual
contraction triangle, independently of reducedness or integrality. -/
@[reassoc] lemma middleBase_on_residue {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of (node π m))) (s : Z ⟶ Spec (.of k))
    (hj : j ≫ base = s ≫ residueBase) :
    j ≫ Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
      s ≫ NextCenter.origin π hπ (m + 2) (by omega) := by
  let a := pullback.lift j s hj
  have H := congrArg (a ≫ ·) (middleSpecialFibre_contracts hπ m)
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd, a] using H

end AlgebraicGeometry.Scheme.PowerNode.Resolution

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {n : ℕ} {hn : 0 < n}
  (C : Chart Y π hπ n hn)

/-- The full original node square identifies every scheme-valued lift
through its centre, retaining the given residue-field map. -/
lemma factor_through_point {Z : Scheme.{u}} (j : Z ⟶ C.C)
    (s : Z ⟶ Spec (.of (ResidueField R)))
    (hj : j ≫ C.toNode = s ≫ NextCenter.origin π hπ n hn) : j = s ≫ C.point := by
  have H := C.node_square.lift_snd j s hj
  simp only [Category.comp_id] at H
  simpa only [H] using (C.node_square.lift_fst j s hj).symm

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
  (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1))) (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)

/-- Full raw-middle contraction through the original common point. -/
@[reassoc] lemma commonMiddle_on_residue {Z : Scheme.{u}}
    (j : Z ⟶ middle C D BC) (s : Z ⟶ Spec (.of (ResidueField R)))
    (hj : j ≫ middleToNode C D BC ≫ Resolution.base = s ≫ Resolution.residueBase) :
    j ≫ middleToCommon C D BC ≫ BC.map = s ≫ C.point := by
  apply C.factor_through_point
  have H := Resolution.middleBase_on_residue hπ m (j ≫ middleToNode C D BC) s
    (by simpa only [Category.assoc] using hj)
  rw [Category.assoc] at H
  simp only [Category.assoc]
  rw [← toNode_triangle, middle_square_assoc, BlowupAtlas.middleChartMap_triangle]
  exact H

/-- After passage to the actual global blowup the whole residue middle
still contracts to the original specified global point. -/
@[reassoc] lemma globalMiddle_on_residue {Z : Scheme.{u}}
    (j : Z ⟶ middle C D BC) (s : Z ⟶ Spec (.of (ResidueField R)))
    (hj : j ≫ middleToNode C D BC ≫ Resolution.base = s ≫ Resolution.residueBase) :
    j ≫ middleToGlobal C D BG BC ≫ BG.map = s ≫ C.globalPoint := by
  simp only [middleToGlobal, Category.assoc, toGlobal_triangle]
  rw [commonMiddle_on_residue_assoc C D BC j s hj, C.point_global]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end -- noncomputable section
end MiddleSpecialContraction

section PointedMiddleSpecialExclusion

/-! An actual arbitrary later morphism into the first global blowup retains
the full middle chart by pullback. Its literal residue chart is etale over
the SAME final residue fibre, and its entire source contracts to the original
specified point. These facts exclude it from an actual punctured-open closure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
  (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1))) (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)
  (hbc : BlowupFlatBaseChange.{u}) (b : Y ⟶ Spec (.of R))
  (hb : C.toGlobal ≫ b = C.toNode ≫ Resolution.base)

include hb in
@[reassoc] lemma rawMiddle_structure :
    middleToGlobal C D BG BC ≫ BG.map ≫ b = middleToNode C D BC ≫ Resolution.base := by
  simp only [middleToGlobal, Category.assoc]
  rw [toGlobal_triangle_assoc, hb, ← toNode_triangle_assoc, middle_square_assoc,
    OneStepBlowup.middleChartMap_base_triangle]

variable {Z : Scheme.{u}} (f : Z ⟶ BG.Y)

/-- The pullback of the middle chart along the given later morphism to the blowup source. -/
abbrev laterMiddle : Scheme.{u} := pullback f (middleToGlobal C D BG BC)
/-- The projection from the pulled-back middle chart to the later source scheme. -/
abbrev laterMiddleMap : laterMiddle C D BG BC f ⟶ Z :=
  pullback.fst f (middleToGlobal C D BG BC)

include hbc in
lemma laterMiddleMap_etale : Etale (laterMiddleMap C D BG BC f) := by
  let := middleToGlobal_etale C D BG BC hbc
  dsimp [laterMiddleMap]
  infer_instance

/-- The residue-field fibre of the later source over its composite base morphism. -/
abbrev laterSpecialFibre : Scheme.{u} :=
  pullback (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R))

/-- Literal pullback of the full retained middle chart to the final residue
fibre. The eventual application takes f to be the actual Run tail map. -/
abbrev laterMiddleSpecial : Scheme.{u} :=
  pullback (laterMiddleMap C D BG BC f)
    (pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R)))

/-- The projection from the pulled-back middle chart on the special fibre to the later special
fibre. -/
abbrev laterMiddleSpecialMap : laterMiddleSpecial C D BG BC b f ⟶ laterSpecialFibre C BG b f :=
  pullback.snd (laterMiddleMap C D BG BC f)
    (pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R)))

include hbc in
/-- Flatness is proved from actual etale base changes; it is not an input
about a chosen component or the final model. -/
lemma laterMiddleSpecialMap_etale : Etale (laterMiddleSpecialMap C D BG BC b f) := by
  let := laterMiddleMap_etale C D BG BC hbc f
  dsimp [laterMiddleSpecialMap]
  infer_instance

/-- The projection from the special-fibre middle pullback to the original middle chart. -/
def laterMiddleSpecialToRaw : laterMiddleSpecial C D BG BC b f ⟶ middle C D BC :=
  pullback.fst (laterMiddleMap C D BG BC f)
    (pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R))) ≫
      pullback.snd f (middleToGlobal C D BG BC)

/-- The residue-field structure morphism of the special-fibre middle pullback. -/
def laterMiddleSpecialBase : laterMiddleSpecial C D BG BC b f ⟶ Spec (.of (ResidueField R)) :=
  laterMiddleSpecialMap C D BG BC b f ≫
    pullback.snd (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R))

@[reassoc] lemma laterMiddleSpecial_raw_triangle :
    laterMiddleSpecialToRaw C D BG BC b f ≫ middleToGlobal C D BG BC =
      laterMiddleSpecialMap C D BG BC b f ≫
        pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R)) ≫ f :=
  ((IsPullback.of_hasPullback (laterMiddleMap C D BG BC f)
    (pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R)))).paste_horiz
      (IsPullback.of_hasPullback f (middleToGlobal C D BG BC)).flip).w

include hb in
lemma laterMiddleSpecial_node_base :
    laterMiddleSpecialToRaw C D BG BC b f ≫ middleToNode C D BC ≫ Resolution.base =
      laterMiddleSpecialBase C D BG BC b f ≫ Resolution.residueBase := by
  rw [← rawMiddle_structure C D BG BC b hb]
  rw [laterMiddleSpecial_raw_triangle_assoc]
  simp only [laterMiddleSpecialBase, Category.assoc, pullback.condition]

include hb in
/-- Exact contraction of the WHOLE retained residue middle chart to the
original global point, for any actual subsequent morphism f. -/
@[reassoc] lemma laterMiddleSpecial_contracts :
    laterMiddleSpecialMap C D BG BC b f ≫
      pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R)) ≫ f ≫ BG.map =
        laterMiddleSpecialBase C D BG BC b f ≫ C.globalPoint := by
  rw [← laterMiddleSpecial_raw_triangle_assoc]
  exact globalMiddle_on_residue C D BG BC _ _
    (laterMiddleSpecial_node_base C D BG BC b hb f)

include hb hbc in
/-- Scheme-theoretic exclusion of this ACTUAL flat residue chart from an
actual punctured-open closure. The remaining disjointness condition concerns
the punctured image in the original scheme, not an assumed component cover. -/
lemma laterMiddleStrictPullback_empty {U : Scheme.{u}}
    (j : U ⟶ laterSpecialFibre C BG b f) [QuasiCompact j] [IsIntegral U]
    (hj : Disjoint (Set.range (j ≫
      pullback.fst (f ≫ BG.map ≫ b) (Resolution.residueBase (R := R)) ≫ f ≫ BG.map))
        (Set.range C.globalPoint)) :
    IsEmpty (pullback (C := Scheme.{u}) (AlgebraicGeometry.Scheme.Hom.imageι j)
      (laterMiddleSpecialMap C D BG BC b f)) := by
  let := laterMiddleSpecialMap_etale C D BG BC hbc b f
  exact AlgebraicGeometry.Scheme.Hom.Image.flatClosurePullback_empty_of_contraction j
    (laterMiddleSpecialMap C D BG BC b f) _ C.globalPoint
    (laterMiddleSpecialBase C D BG BC b f)
    (laterMiddleSpecial_contracts C D BG BC b hb f) hj

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end -- noncomputable section
end PointedMiddleSpecialExclusion

section PointedOuterStrictComparison

/-! Transport the computed literal outer puncture through the actual pointed
common-chart squares. The resulting closure comparison is constructed from
flat image base change, with the full scheme pullbacks and exact projection.
No integral or affine-line claim is made about an arbitrary etale pullback. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {n : ℕ} {hn : 0 < n}
  (C : Chart Y π hπ n hn)

/-- The same point is pulled back on both sides of the genuine common chart. -/
lemma original_node_preimage_eq :
    C.toGlobal ⁻¹' Set.range C.globalPoint =
      C.toNode ⁻¹' Set.range (NextCenter.origin π hπ n hn) := by
  have HG : Set.range C.point = C.toGlobal ⁻¹' Set.range C.globalPoint := by
    rw [← C.global_square.isoPullback_hom_fst]
    change Set.range ((pullback.fst C.toGlobal C.globalPoint) ∘ C.global_square.isoPullback.hom) = _
    have hs : Function.Surjective C.global_square.isoPullback.hom :=
      C.global_square.isoPullback.hom.homeomorph.surjective
    rw [hs.range_comp, Scheme.Pullback.range_fst]
  have HN : Set.range C.point =
      C.toNode ⁻¹' Set.range (NextCenter.origin π hπ n hn) := by
    rw [← C.node_square.isoPullback_hom_fst]
    change Set.range ((pullback.fst C.toNode _) ∘ C.node_square.isoPullback.hom) = _
    have hs : Function.Surjective C.node_square.isoPullback.hom :=
      C.node_square.isoPullback.hom.homeomorph.surjective
    rw [hs.range_comp, Scheme.Pullback.range_fst]
  exact HG.symm.trans HN

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
  (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1)))
  {U X Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U]
  (b : X ⟶ Y) (g : Z ⟶ X) [Flat g] (a : Z ⟶ C.C)
  (t : Z ⟶ Resolution.outerFibre (π := π)) [Flat t]
  (d : Resolution.outerFibre (π := π) ⟶ Spec (.of (node π (m + 2))))
  (hj : Set.range j = b ⁻¹' (Set.range C.globalPoint)ᶜ)
  (hd : Set.range (Resolution.outerStrictPuncture hπ) =
    d ⁻¹' (Set.range (NextCenter.origin π hπ (m + 2) (Nat.succ_pos (m + 1))))ᶜ)
  (hglobal : g ≫ b = a ≫ C.toGlobal) (hnode : a ≫ C.toNode = t ≫ d)

omit [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U] [Flat g] [Flat t] in
include hj hd hglobal hnode in
/-- Equality of the two actual pulled-back opens, derived from the exact
point squares and contraction triangles. -/
lemma outer_pulled_puncture_range :
    Set.range (pullback.snd j g) =
      Set.range (pullback.snd (Resolution.outerStrictPuncture hπ) t) := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hj, hd]
  have H : (g ≫ b) ⁻¹' Set.range C.globalPoint =
      (t ≫ d) ⁻¹' Set.range (NextCenter.origin π hπ (m + 2) (by omega)) := by
    rw [hglobal, ← hnode]
    exact congrArg (fun s => a ⁻¹' s) (C.original_node_preimage_eq)
  exact congrArg (fun s => sᶜ) H

/-- Constructed scheme-theoretic identification with the FULL actual branch
pullback, rather than with an assumed affine component. -/
def outerStrictPullbackIso :
    pullback (AlgebraicGeometry.Scheme.Hom.imageι j) g ≅
      pullback t (Resolution.outerEndBranch hπ) :=
  (AlgebraicGeometry.Scheme.Hom.Image.flatBaseChangeIso j g).symm ≪≫
    AlgebraicGeometry.Scheme.Hom.Image.openImageIso (pullback.snd j g)
      (pullback.snd (Resolution.outerStrictPuncture hπ) t)
      (outer_pulled_puncture_range C j b g a t d hj hd hglobal hnode) ≪≫
    Resolution.flatOuterStrictClosureIso hπ t

@[reassoc] lemma outerStrictPullbackIso_hom_fst :
    (outerStrictPullbackIso C j b g a t d hj hd hglobal hnode).hom ≫
      pullback.fst t (Resolution.outerEndBranch hπ) =
        pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) g := by
  simp only [outerStrictPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Resolution.flatOuterStrictClosureIso_hom_fst,
    AlgebraicGeometry.Scheme.Hom.Image.openImageIso_hom_inclusion]
  have H := congrArg (fun q => (AlgebraicGeometry.Scheme.Hom.Image.flatBaseChangeIso j g).inv ≫ q)
    (AlgebraicGeometry.Scheme.Hom.Image.flatBaseChangeIso_hom_snd j g)
  simpa only [Iso.inv_hom_id_assoc] using H.symm

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end -- noncomputable section
end PointedOuterStrictComparison

section PointedRawOuterCharts

/-! Actual full first outer common charts on both sides. Their maps are literal
pullback projections, and their factors through the whole outer open are proved.
No connectedness, integrality, affine-line, or component premise is imposed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {π : R} {m : ℕ} (D : OneStepBlowup.Data π m) (hπ : Irreducible π)

/-- False denotes the first left chart; true denotes the first right chart. -/
def firstOuterChartMap (side : Bool) : Spec (.of (PlaneNode.Ring π)) ⟶ D.blowup.Y :=
  if side then BlowupAtlas.rightChartMap D.atlas hπ
  else BlowupAtlas.leftChartMap D.atlas hπ

instance firstOuterChartMap_open (side : Bool) : IsOpenImmersion (firstOuterChartMap D hπ side) :=
  by
  cases side <;> simp only [firstOuterChartMap, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

lemma firstOuterChartMap_mem_outer (side : Bool) (z : Spec (.of (PlaneNode.Ring π))) :
    firstOuterChartMap D hπ side z ∈ outerOpen D hπ := by
  cases side
  · exact Or.inl ⟨z, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

@[reassoc] lemma firstOuterChartMap_base (side : Bool) :
    firstOuterChartMap D hπ side ≫ D.blowup.map ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) := by
  cases side
  · exact OneStepBlowup.leftChartMap_base_triangle D hπ
  · exact OneStepBlowup.rightChartMap_base_triangle D hπ

/-- The morphism from the chosen first outer fibre to the original exponent-`m + 2` node. -/
def firstOuterOriginal (m : ℕ) (side : Bool) :
    outerFibre (π := π) ⟶ Spec (.of (node π (m + 2))) :=
  if side then outerRightOriginal (π := π) m else outerLeftOriginal (π := π) m

lemma firstOuterOriginal_puncture_range (m : ℕ) (side : Bool) :
    Set.range (outerStrictPuncture hπ) = firstOuterOriginal (π := π) m side ⁻¹'
      (Set.range (NextCenter.origin π hπ (m + 2) (by omega)))ᶜ := by
  cases side
  · exact outerLeftOriginal_puncture_range hπ m
  · exact outerRightOriginal_puncture_range hπ m

end AlgebraicGeometry.Scheme.PowerNode.Resolution
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
  (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1))) (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center) (side : Bool)

/-- The pullback of the chosen first outer node chart to the common blowup source. -/
def rawOuter : Scheme.{u} :=
  pullback (toNode C D BC) (Resolution.firstOuterChartMap D hπ side)
/-- The projection from the raw outer pullback to the common blowup source. -/
def rawOuterToCommon : rawOuter C D BC side ⟶ BC.Y := pullback.fst _ _
/-- The projection from the raw outer pullback to the uniformizer node chart. -/
def rawOuterToNode : rawOuter C D BC side ⟶ Spec (.of (PlaneNode.Ring π)) := pullback.snd _ _
/-- The raw outer chart mapped through the common blowup into the global blowup source. -/
def rawOuterToGlobal : rawOuter C D BC side ⟶ BG.Y := rawOuterToCommon C D BC side ≫ toGlobal C BG
  BC

instance rawOuterToCommon_open : IsOpenImmersion (rawOuterToCommon C D BC side) := by
  dsimp [rawOuterToCommon]; infer_instance

@[reassoc] lemma rawOuter_square :
    rawOuterToCommon C D BC side ≫ toNode C D BC =
      rawOuterToNode C D BC side ≫ Resolution.firstOuterChartMap D hπ side := pullback.condition

lemma rawOuterToNode_etale (hbc : BlowupFlatBaseChange.{u}) :
    Etale (rawOuterToNode C D BC side) := by
  let := toNode_etale C D BC hbc
  dsimp [rawOuterToNode]; infer_instance
lemma rawOuterToGlobal_etale (hbc : BlowupFlatBaseChange.{u}) :
    Etale (rawOuterToGlobal C D BG BC side) := by
  let := toGlobal_etale C BG BC hbc
  dsimp [rawOuterToGlobal]; infer_instance

/-- The inverse image of the node outer open in the common blowup source. -/
def rawOuterOpen : BC.Y.Opens := toNode C D BC ⁻¹ᵁ Resolution.outerOpen D hπ

lemma rawOuter_range_subset_outer : Set.range (rawOuterToCommon C D BC side) ⊆
    rawOuterOpen C D BC := by
  rintro _ ⟨z, rfl⟩
  change (rawOuterToCommon C D BC side ≫ toNode C D BC) z ∈ Resolution.outerOpen D hπ
  rw [rawOuter_square]
  exact Resolution.firstOuterChartMap_mem_outer D hπ side _

/-- The whole raw chart, not merely its exceptional locus, factors through the
whole first outer open used by the unchanged-tail theorem. -/
def rawOuterToOuterOpen : rawOuter C D BC side ⟶ (rawOuterOpen C D BC).toScheme :=
  IsOpenImmersion.lift (rawOuterOpen C D BC).ι (rawOuterToCommon C D BC side)
    (by simpa only [Scheme.Opens.range_ι] using rawOuter_range_subset_outer C D BC side)

@[reassoc] lemma rawOuterToOuterOpen_triangle :
    rawOuterToOuterOpen C D BC side ≫ (rawOuterOpen C D BC).ι =
      rawOuterToCommon C D BC side := IsOpenImmersion.lift_fac _ _ _

variable (b : Y ⟶ Spec (.of R))
  (hb : C.toGlobal ≫ b = C.toNode ≫ Resolution.base)
include hb in
@[reassoc] lemma rawOuter_structure :
    rawOuterToGlobal C D BG BC side ≫ BG.map ≫ b =
      rawOuterToNode C D BC side ≫ Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))
        := by
  simp only [rawOuterToGlobal, Category.assoc]
  rw [toGlobal_triangle_assoc, hb, ← toNode_triangle_assoc, rawOuter_square_assoc,
    Resolution.firstOuterChartMap_base]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end -- noncomputable section
end PointedRawOuterCharts

section PointedRetainedOuterCharts

/-! Entire actual first outer charts retained through the exact finite Run.
Thickness two has the identity tail. Higher thickness uses the already-proved
unchanged current-centre complement, with no additional retention assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

lemma firstRawOuter_disjoint {m : ℕ} (S : State X q₀ π hπ (m + 3) (by omega)) (side : Bool) :
    Disjoint (Set.range (Chart.Step.rawOuterToGlobal S.chart
      (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) (S.blowup hex) (S.commonBlowup hex) side))
      (Set.range (S.step hex hp hatlas hbc (by omega : 0 < m + 1)).chart.globalPoint) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ hz
  apply Set.disjoint_left.mp (Run.Step.currentOuter_disjoint S hex hp hatlas hbc) _ hz
  refine ⟨Chart.Step.rawOuterToOuterOpen S.chart
    (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) (S.commonBlowup hex) side a, ?_⟩
  change (Chart.Step.rawOuterToOuterOpen S.chart
    (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) (S.commonBlowup hex) side ≫
      (Chart.Step.rawOuterOpen S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
        (S.commonBlowup hex)).ι ≫
        Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex)) a = _
  rw [Chart.Step.rawOuterToOuterOpen_triangle_assoc]
  rfl

/-- Constructor-level retention avoids rewriting a canonical recursive Run
inside its dependent source scheme. The only argument is the actual finite Run. -/
lemma firstActualOuterProjection_isIso {m : ℕ}
    {S : State X q₀ π hπ (m + 2) (by omega)}
    (T : Run hex hp hatlas hbc S) (side : Bool) :
    IsIso (pullback.snd (T.afterFirstMap (by omega))
      (Chart.Step.rawOuterToGlobal S.chart (OneStepBlowup.ofFamilies π m hex hp hatlas)
        (S.blowup hex) (S.commonBlowup hex) side)) := by
  cases T with
  | two S =>
      change IsIso (pullback.snd (𝟙 _) _)
      infer_instance
  | next m S tail =>
      exact Run.retained_projection_isIso tail _
        (firstRawOuter_disjoint hex hp hatlas hbc S side)

variable (m : ℕ) (S : State X q₀ π hπ (m + 2) (Nat.succ_pos (m + 1))) (side : Bool)
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "BG" => S.blowup hex
local notation "BC" => S.commonBlowup hex
local notation "f" => runAfterFirstMap hex hp hatlas hbc m S
local notation "a" => Chart.Step.rawOuterToGlobal S.chart D BG BC side
local notation "T" => run hex hp hatlas hbc (m + 2) (by omega) S

/-- The first raw outer chart pulled back along the remaining resolution morphism. -/
abbrev firstRetainedOuter : Scheme.{u} := pullback f a
/-- The projection from the retained first outer chart to the final run source. -/
abbrev firstRetainedOuterMap : firstRetainedOuter hex hp hatlas hbc m S side ⟶ (T).source :=
  pullback.fst f a
/-- The projection from the retained first outer chart to the raw outer chart. -/
abbrev firstRetainedOuterToRaw : firstRetainedOuter hex hp hatlas hbc m S side ⟶
    Chart.Step.rawOuter S.chart D BC side := pullback.snd f a

/-- This is proved for the literal full pullback and both raw outer charts. -/
lemma firstRetainedOuterToRaw_isIso : IsIso (firstRetainedOuterToRaw hex hp hatlas hbc m S side) :=
  firstActualOuterProjection_isIso hex hp hatlas hbc
    (run hex hp hatlas hbc (m + 2) (by omega) S) side

lemma firstRetainedOuterMap_etale : Etale (firstRetainedOuterMap hex hp hatlas hbc m S side) := by
  let := Chart.Step.rawOuterToGlobal_etale S.chart D BG BC side hbc
  dsimp only [firstRetainedOuterMap]
  infer_instance

/-- The retained first outer chart mapped to the uniformizer node through its raw-chart
projection. -/
def firstRetainedOuterToNode : firstRetainedOuter hex hp hatlas hbc m S side ⟶
    Spec (.of (PlaneNode.Ring π)) :=
  firstRetainedOuterToRaw hex hp hatlas hbc m S side ≫ Chart.Step.rawOuterToNode S.chart D BC side

lemma firstRetainedOuterToNode_etale : Etale (firstRetainedOuterToNode hex hp hatlas hbc m S side)
  := by
  let := firstRetainedOuterToRaw_isIso hex hp hatlas hbc m S side
  let := Chart.Step.rawOuterToNode_etale S.chart D BC side hbc
  dsimp only [firstRetainedOuterToNode]
  infer_instance

/-- The retained first outer chart mapped to the initial common chart through the common blowup. -/
def firstRetainedOuterToCommon : firstRetainedOuter hex hp hatlas hbc m S side ⟶ S.chart.C :=
  firstRetainedOuterToRaw hex hp hatlas hbc m S side ≫
    Chart.Step.rawOuterToCommon S.chart D BC side ≫ (BC).map

@[reassoc] lemma firstRetainedOuter_global :
    firstRetainedOuterMap hex hp hatlas hbc m S side ≫ f ≫ (BG).map =
      firstRetainedOuterToCommon hex hp hatlas hbc m S side ≫ S.chart.toGlobal := by
  rw [← Category.assoc, pullback.condition]
  simp only [Chart.Step.rawOuterToGlobal, firstRetainedOuterToCommon, firstRetainedOuterToRaw,
    Category.assoc,
    Chart.Step.toGlobal_triangle]

variable (b : S.Y ⟶ Spec (.of R))
  (hb : S.chart.toGlobal ≫ b = S.chart.toNode ≫ Resolution.base)
include hb in
@[reassoc] lemma firstRetainedOuter_structure :
    firstRetainedOuterMap hex hp hatlas hbc m S side ≫ f ≫ (BG).map ≫ b =
      firstRetainedOuterToNode hex hp hatlas hbc m S side ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) := by
  rw [← Category.assoc (firstRetainedOuterMap hex hp hatlas hbc m S side), pullback.condition]
  simp only [Category.assoc, firstRetainedOuterToNode]
  rw [Chart.Step.rawOuter_structure S.chart D BG BC side b hb]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end PointedRetainedOuterCharts

section PointedRetainedOuterSpecial

/-! Residue base change of the entire retained first outer chart. Both maps are
actual etale maps, and the exact original chart triangles are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (m : ℕ) (S : State X q₀ π hπ (m + 2) (Nat.succ_pos (m + 1))) (side : Bool)
  (b : S.Y ⟶ Spec (.of R))
  (hb : S.chart.toGlobal ≫ b = S.chart.toNode ≫ Resolution.base)
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "BG" => S.blowup hex
local notation "BC" => S.commonBlowup hex
local notation "f" => runAfterFirstMap hex hp hatlas hbc m S
local notation "r" => Resolution.residueBase (R := R)
local notation "Nbase" => Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))
local notation "rmap" => firstRetainedOuterMap hex hp hatlas hbc m S side
local notation "rnode" => firstRetainedOuterToNode hex hp hatlas hbc m S side

/-- The residue-field pullback of the retained first outer chart. -/
abbrev firstOuterSpecial : Scheme.{u} := pullback rmap (pullback.fst (f ≫ (BG).map ≫ b) r)
/-- The projection from the retained first outer special fibre to the final run special fibre. -/
abbrev firstOuterSpecialMap : firstOuterSpecial hex hp hatlas hbc m S side b ⟶
    pullback (f ≫ (S.blowup hex).map ≫ b) r :=
  pullback.snd rmap (pullback.fst (f ≫ (BG).map ≫ b) r)
/-- The projection from the retained first outer special fibre to the retained outer chart. -/
abbrev firstOuterSpecialToRetained : firstOuterSpecial hex hp hatlas hbc m S side b ⟶
    firstRetainedOuter hex hp hatlas hbc m S side :=
  pullback.fst rmap (pullback.fst (f ≫ (BG).map ≫ b) r)

/-- The residue-field structure morphism of the retained first outer special fibre. -/
def firstOuterSpecialBase : firstOuterSpecial hex hp hatlas hbc m S side b ⟶ Spec (.of
  (ResidueField R)) :=
  firstOuterSpecialMap hex hp hatlas hbc m S side b ≫ pullback.snd (f ≫ (BG).map ≫ b) r

/-- The retained first outer special fibre mapped to the initial common chart. -/
def firstOuterSpecialToCommon : firstOuterSpecial hex hp hatlas hbc m S side b ⟶ S.chart.C :=
  firstOuterSpecialToRetained hex hp hatlas hbc m S side b ≫
    firstRetainedOuterToCommon hex hp hatlas hbc m S side

lemma firstOuterSpecialMap_etale : Etale (firstOuterSpecialMap hex hp hatlas hbc m S side b) := by
  let := firstRetainedOuterMap_etale hex hp hatlas hbc m S side
  dsimp only [firstOuterSpecialMap]
  infer_instance

include hb in
lemma firstOuterSpecial_node_base :
    firstOuterSpecialToRetained hex hp hatlas hbc m S side b ≫ rnode ≫ Nbase =
      firstOuterSpecialBase hex hp hatlas hbc m S side b ≫ r := by
  rw [← firstRetainedOuter_structure hex hp hatlas hbc m S side b hb]
  simp only [firstOuterSpecialToRetained, firstOuterSpecialBase, firstOuterSpecialMap]
  rw [← Category.assoc, pullback.condition]
  simp only [Category.assoc, pullback.condition]

/-- The literal map to the same nodal outer residue fibre on either side. -/
def firstOuterSpecialToNode : firstOuterSpecial hex hp hatlas hbc m S side b ⟶
    Resolution.outerFibre (π := π) :=
  pullback.lift (firstOuterSpecialToRetained hex hp hatlas hbc m S side b ≫ rnode)
    (firstOuterSpecialBase hex hp hatlas hbc m S side b)
    (firstOuterSpecial_node_base hex hp hatlas hbc m S side b hb)

@[reassoc (attr := simp)] lemma firstOuterSpecialToNode_fst :
    firstOuterSpecialToNode hex hp hatlas hbc m S side b hb ≫ pullback.fst Nbase r =
      firstOuterSpecialToRetained hex hp hatlas hbc m S side b ≫ rnode := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma firstOuterSpecialToNode_snd :
    firstOuterSpecialToNode hex hp hatlas hbc m S side b hb ≫ pullback.snd Nbase r =
      firstOuterSpecialBase hex hp hatlas hbc m S side b := pullback.lift_snd ..

lemma firstOuterSpecial_node_square :
    IsPullback (firstOuterSpecialToRetained hex hp hatlas hbc m S side b)
      (firstOuterSpecialToNode hex hp hatlas hbc m S side b hb) rnode (pullback.fst Nbase r) := by
  have H : IsPullback (firstOuterSpecialToRetained hex hp hatlas hbc m S side b)
      (firstOuterSpecialToNode hex hp hatlas hbc m S side b hb ≫ pullback.snd Nbase r)
      (rnode ≫ Nbase) r := by
    rw [firstOuterSpecialToNode_snd, ← firstRetainedOuter_structure hex hp hatlas hbc m S side b hb]
    exact (IsPullback.of_hasPullback rmap (pullback.fst (f ≫ (BG).map ≫ b) r)).paste_vert
      (IsPullback.of_hasPullback (f ≫ (BG).map ≫ b) r)
  exact H.of_bot (firstOuterSpecialToNode_fst hex hp hatlas hbc m S side b hb).symm
    (IsPullback.of_hasPullback Nbase r)

lemma firstOuterSpecialToNode_etale : Etale (firstOuterSpecialToNode hex hp hatlas hbc m S side b
  hb) := by
  let := firstRetainedOuterToNode_etale hex hp hatlas hbc m S side
  exact MorphismProperty.of_isPullback (P := @Etale)
    (firstOuterSpecial_node_square hex hp hatlas hbc m S side b hb) inferInstance

@[reassoc] lemma firstOuterSpecial_global :
    firstOuterSpecialMap hex hp hatlas hbc m S side b ≫
      pullback.fst (f ≫ (BG).map ≫ b) r ≫ f ≫ (BG).map =
      firstOuterSpecialToCommon hex hp hatlas hbc m S side b ≫ S.chart.toGlobal := by
  rw [← Category.assoc, ← pullback.condition]
  simp only [Category.assoc, firstRetainedOuter_global, firstOuterSpecialToCommon,
    firstOuterSpecialToRetained]

@[reassoc] lemma firstOuterSpecial_original_node :
    firstOuterSpecialToCommon hex hp hatlas hbc m S side b ≫ S.chart.toNode =
      firstOuterSpecialToNode hex hp hatlas hbc m S side b hb ≫
        Resolution.firstOuterOriginal (π := π) m side := by
  have H : firstRetainedOuterToCommon hex hp hatlas hbc m S side ≫ S.chart.toNode =
      rnode ≫ Resolution.firstOuterChartMap D hπ side ≫ (D).blowup.map := by
    simp only [firstRetainedOuterToCommon, firstRetainedOuterToNode, Category.assoc]
    rw [← Chart.Step.toNode_triangle, Chart.Step.rawOuter_square_assoc]
  cases side
  · simp only [Resolution.firstOuterOriginal, Bool.false_eq_true, ↓reduceIte,
      Resolution.outerLeftOriginal, firstOuterSpecialToCommon, Category.assoc,
      firstOuterSpecialToNode_fst_assoc]
    rw [H]
    simp only [Resolution.firstOuterChartMap, Bool.false_eq_true, ↓reduceIte,
      BlowupAtlas.leftChartMap_triangle]
  · simp only [Resolution.firstOuterOriginal, ↓reduceIte,
      Resolution.outerRightOriginal, firstOuterSpecialToCommon, Category.assoc,
      firstOuterSpecialToNode_fst_assoc]
    rw [H]
    simp only [Resolution.firstOuterChartMap, ↓reduceIte,
      BlowupAtlas.rightChartMap_triangle]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end PointedRetainedOuterSpecial

section PointedFirstSpecialCover

/-! Actual first-chart coverage over the original point. The common chart is
used only over that point, by its full exceptional pullback square. Arbitrary
later points are lifted by the two literal pullback range identities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
  (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1))) (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)
  (hbc : BlowupFlatBaseChange.{u})

include hbc in
/-- Whole raw left/middle/right cover above the original centre; no global
surjectivity of the original common etale chart is asserted or assumed. -/
lemma rawFirstCharts_cover (z : BG.Y) (hz : BG.map z ∈ Set.range C.globalPoint) :
    z ∈ Set.range (rawOuterToGlobal C D BG BC false) ∨
      z ∈ Set.range (middleToGlobal C D BG BC) ∨
        z ∈ Set.range (rawOuterToGlobal C D BG BC true) := by
  obtain ⟨w, hw⟩ := covers_exceptional C BG BC hbc z hz
  rcases BlowupAtlas.three_charts_cover D.atlas hπ (toNode C D BC w) with hl | hm | hr
  · left
    have H : w ∈ Set.range (rawOuterToCommon C D BC false) := by
      change w ∈ Set.range (pullback.fst (toNode C D BC)
        (Resolution.firstOuterChartMap D hπ false))
      rw [Scheme.Pullback.range_fst]
      exact hl
    obtain ⟨v, hv⟩ := H
    exact ⟨v, (congrArg (toGlobal C BG BC) hv).trans hw⟩
  · right; left
    have H : w ∈ Set.range (middleToCommon C D BC) := by
      change w ∈ Set.range (pullback.fst (toNode C D BC) (BlowupAtlas.middleChartMap D.atlas hπ))
      rw [Scheme.Pullback.range_fst]
      exact hm
    obtain ⟨v, hv⟩ := H
    exact ⟨v, (congrArg (toGlobal C BG BC) hv).trans hw⟩
  · right; right
    have H : w ∈ Set.range (rawOuterToCommon C D BC true) := by
      change w ∈ Set.range (pullback.fst (toNode C D BC)
        (Resolution.firstOuterChartMap D hπ true))
      rw [Scheme.Pullback.range_fst]
      exact hr
    obtain ⟨v, hv⟩ := H
    exact ⟨v, (congrArg (toGlobal C BG BC) hv).trans hw⟩

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (m : ℕ) (S : State X q₀ π hπ (m + 2) (Nat.succ_pos (m + 1)))
  (b : S.Y ⟶ Spec (.of R))
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "BG" => S.blowup hex
local notation "BC" => S.commonBlowup hex
local notation "f" => runAfterFirstMap hex hp hatlas hbc m S
local notation "r" => Resolution.residueBase (R := R)

lemma firstOuterSpecial_range (side : Bool) :
    Set.range (firstOuterSpecialMap hex hp hatlas hbc m S side b) =
      (pullback.fst (f ≫ (BG).map ≫ b) r ≫ f) ⁻¹'
        Set.range (Chart.Step.rawOuterToGlobal S.chart D BG BC side) := by
  change Set.range (pullback.snd (pullback.fst f _)
    (pullback.fst (f ≫ (BG).map ≫ b) r)) = _
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_fst]
  rfl

lemma firstMiddleSpecial_range :
    Set.range (Chart.Step.laterMiddleSpecialMap S.chart D BG BC b f) =
      (pullback.fst (f ≫ (BG).map ≫ b) r ≫ f) ⁻¹'
        Set.range (Chart.Step.middleToGlobal S.chart D BG BC) := by
  change Set.range (pullback.snd (pullback.fst f _)
    (pullback.fst (f ≫ (BG).map ≫ b) r)) = _
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_fst]
  rfl

/-- The entire retained first left/middle/right special charts cover every
point contracting to the original centre, in the literal same residue fibre. -/
lemma firstSpecialCharts_cover
    (z : pullback (C := Scheme.{u}) (runAfterFirstMap hex hp hatlas hbc m S ≫ (S.blowup hex).map ≫
      b)
      (Resolution.residueBase (R := R)))
    (hz : (pullback.fst (f ≫ (BG).map ≫ b) r ≫ f ≫ (BG).map) z ∈
      Set.range S.chart.globalPoint) :
    z ∈ Set.range (firstOuterSpecialMap hex hp hatlas hbc m S false b) ∨
      z ∈ Set.range (Chart.Step.laterMiddleSpecialMap S.chart D BG BC b f) ∨
        z ∈ Set.range (firstOuterSpecialMap hex hp hatlas hbc m S true b) := by
  rw [firstOuterSpecial_range, firstOuterSpecial_range, firstMiddleSpecial_range]
  exact Chart.Step.rawFirstCharts_cover S.chart D BG BC hbc
    ((pullback.fst (f ≫ (BG).map ≫ b) r ≫ f) z) hz

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end PointedFirstSpecialCover
