/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveImage
public import Aglib.AlgebraicGeometry.Morphisms.FiniteType.FieldPoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Noncollapse of contracted curves on a finite common graph

A finite map to the literal fibre product makes each closed fibre finite
over the previous model. Discrete fibres prohibit simultaneous contraction
of an actual curve by both projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- The original map from a closed point through a proper morphism is finite.
The proof uses the original residue field, not an algebraic closure. -/
theorem closedPoint_comp_isFinite {S T : Scheme.{u}}
    (r : S ⟶ T) [IsProper r] (s : S) (hs : IsClosed ({s} : Set S)) :
    IsFinite (S.fromSpecResidueField s ≫ r) := by
  let : IsClosedImmersion (S.fromSpecResidueField s) :=
    isClosed_singleton_iff_isClosedImmersion.mp hs
  let c := S.fromSpecResidueField s ≫ r
  have hclosed : IsClosed ({c (IsLocalRing.closedPoint (S.residueField s))} : Set T) := by
    simpa only [Set.image_singleton] using
      c.isClosedMap {IsLocalRing.closedPoint (S.residueField s)} isClosed_singleton
  exact c.isFinite_of_field_of_isClosed_image hclosed

/-- A finite actual graph pair induces a finite map from each closed fibre
of the first projection to the second model. The two cartesian squares and
all arrows are the literal scheme pullbacks. -/
theorem closedFiber_toTarget_isFinite
    {X Y S T : Scheme.{u}} (p : X ⟶ S) (g : X ⟶ Y)
    (r : S ⟶ T) [IsProper r] (q : Y ⟶ T) (w : p ≫ r = g ≫ q)
    [IsFinite (pullback.lift p g w)] (s : S) (hs : IsClosed ({s} : Set S)) :
    IsFinite (p.fiberι s ≫ g) := by
  let c := S.fromSpecResidueField s
  let k := pullback.lift p g w
  let a := pullback.fst r q
  let b := pullback.snd r q
  let B := pullback a c
  let m : p.fiber s ⟶ B := pullback.lift (p.fiberι s ≫ k)
    (p.fiberToSpecResidueField s) (by
      simpa only [Category.assoc, k, a, c, pullback.lift_fst] using p.fiber_fac s)
  have hm_fst : m ≫ pullback.fst a c = p.fiberι s ≫ k := by simp [m]
  have hm_snd : m ≫ pullback.snd a c = p.fiberToSpecResidueField s := by simp [m]
  have H : IsPullback (p.fiberι s) m k (pullback.fst a c) := by
    have H' : IsPullback (p.fiberι s) (m ≫ pullback.snd a c) (k ≫ a) c := by
      rw [hm_snd]
      have hka : k ≫ a = p := by simp [k, a]
      rw [hka]
      exact IsPullback.of_hasPullback p c
    exact H'.of_bot hm_fst.symm (IsPullback.of_hasPullback a c)
  let : IsFinite m := MorphismProperty.of_isPullback H inferInstance
  let : IsFinite (c ≫ r) := closedPoint_comp_isFinite r s hs
  have H' : IsPullback (pullback.fst a c ≫ b) (pullback.snd a c) q (c ≫ r) :=
    (IsPullback.of_hasPullback a c).paste_horiz (IsPullback.of_hasPullback r q).flip
  let : IsFinite (pullback.fst a c ≫ b) :=
    MorphismProperty.of_isPullback H'.flip inferInstance
  have he : m ≫ (pullback.fst a c ≫ b) = p.fiberι s ≫ g := by
    rw [← Category.assoc, hm_fst, Category.assoc]
    simp [k, b]
  rw [← he]
  infer_instance

/-- An actual curve contracted by the first projection cannot also collapse
under the second projection when the common graph pair is finite. -/
theorem not_subsingleton_image_of_finite_pair
    {X Y S T : Scheme.{u}} (p : X ⟶ S) [IsProper p] (g : X ⟶ Y)
    (r : S ⟶ T) [IsProper r] (q : Y ⟶ T) (w : p ≫ r = g ≫ q)
    [IsFinite (pullback.lift p g w)]
    (C : IrreducibleCloseds X) (hC : C ∈ contractedCurves p) :
    ¬ (g '' (C : Set X)).Subsingleton := by
  intro hg
  obtain ⟨x, hx⟩ := C.isIrreducible.nonempty
  let s := p x
  let y := g x
  have hpC : p '' (C : Set X) = {s} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hC.2 hz ⟨x, hx, rfl⟩
    · exact Set.singleton_subset_iff.mpr ⟨x, hx, rfl⟩
  have hs : IsClosed ({s} : Set S) := hpC ▸ p.isClosedMap _ C.isClosed
  let a := p.fiberι s ≫ g
  let : IsFinite a := closedFiber_toTarget_isFinite p g r q w s hs
  have hdisc : _root_.IsDiscrete ((p.fiberι s) '' (a ⁻¹' {y})) :=
    (a.isDiscrete_preimage_singleton y).image (p.fiberι s).isEmbedding.toIsInducing
  have hsub : (C : Set X) ⊆ (p.fiberι s) '' (a ⁻¹' {y}) := by
    intro z hz
    have hpz : p z = s := hC.2 ⟨z, hz, rfl⟩ ⟨x, hx, rfl⟩
    have hzrange : z ∈ Set.range (p.fiberι s) := by
      rw [p.range_fiberι s]
      exact hpz
    obtain ⟨z', hz'⟩ := hzrange
    refine ⟨z', ?_, hz'⟩
    change g (p.fiberι s z') = y
    rw [hz']
    exact hg ⟨z, hz, rfl⟩ ⟨x, hx, rfl⟩
  have hss : (C : Set X).Subsingleton :=
    (hdisc.mono hsub).subsingleton_of_isPreirreducible C.isIrreducible.isPreirreducible
  let : Subsingleton (C : Set X) := ⟨fun a b ↦ Subtype.ext (hss a.property b.property)⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology (C : Set X)
  rw [hC.1] at hd
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hd

/-- The complete different-source contracted-curve embedding for a finite common
graph. Noncollapse, curve membership and codimension-one uniqueness are all
proved, not supplied. The value is the actual proper image under `g`. -/
def finitePairContractedCurveEmbedding
    {X Y S T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian S]
    (p : X ⟶ S) [IsProper p] [IsDominant p]
    (hp : IsIso (CommRingCat.ofHom (functionFieldMap p))) (hS : NormalStalks S)
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (q : Y ⟶ T) (r : S ⟶ T) [IsProper r] (w : p ≫ r = g ≫ q)
    [IsFinite (pullback.lift p g w)] : contractedCurves p ↪ contractedCurves q where
  toFun C := ⟨g.irreducibleClosedImage C.val,
    Hom.irreducibleClosedImage_mem_contractedCurves p hp hS g hg hY hdY q r w.symm
      C.val C.property (not_subsingleton_image_of_finite_pair p g r q w C.val C.property)⟩
  inj' := by
    intro C D he
    apply Subtype.ext
    exact g.irreducibleClosedImage_injective_of_not_subsingleton hg hY hdY C.val D.val
      (not_subsingleton_image_of_finite_pair p g r q w C.val C.property)
      (congrArg Subtype.val he)

/-- A missing old curve gives strict decrease of the actual curve counts on
different schemes. Finiteness of the new set is derived from the geometric
embedding and the old geometric finiteness theorem. -/
theorem contractedCurveCount_lt_of_finitePair_missing_curve
    {X Y S T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S] [IsIntegral T]
    [IsNoetherian Y] [IsLocallyNoetherian S] [IsLocallyNoetherian T]
    (p : X ⟶ S) [IsProper p] [IsDominant p]
    (hp : IsIso (CommRingCat.ofHom (functionFieldMap p))) (hS : NormalStalks S)
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (q : Y ⟶ T) [IsProper q] [IsDominant q]
    (hq : IsIso (CommRingCat.ofHom (functionFieldMap q))) (hT : NormalStalks T)
    (r : S ⟶ T) [IsProper r] (w : p ≫ r = g ≫ q)
    [IsFinite (pullback.lift p g w)] (C : contractedCurves q)
    (hmiss : C ∉ Set.range (finitePairContractedCurveEmbedding p hp hS g hg hY hdY q r w)) :
    contractedCurveCount p < contractedCurveCount q := by
  let e := finitePairContractedCurveEmbedding p hp hS g hg hY hdY q r w
  let : Finite (contractedCurves q) := (finite_contractedCurves q hq hT hdY).to_subtype
  let : Finite (contractedCurves p) := Finite.of_injective e e.injective
  let : Fintype (contractedCurves p) := Fintype.ofFinite _
  let : Fintype (contractedCurves q) := Fintype.ofFinite _
  simpa only [contractedCurveCount, Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem e e.injective hmiss

end AlgebraicGeometry.Scheme.NormalizedPointDomination
