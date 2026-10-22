/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.AlgebraicGeometry.Morphisms.Proper.QuasiFinite
public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Mathlib.Data.Set.Card
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Actual contracted curves and their finite count

The curves are actual closed irreducible subsets with one-dimensional
subspace topology and subsingleton image under the original morphism.
Finiteness is proved, and the cardinal is used only with that proof.
The original finite-fibre criterion detects isomorphisms when none occur.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Order IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/-- Actual closed irreducible curves contracted by the original morphism. -/
def contractedCurves {X Y : Scheme.{u}} (f : X ⟶ Y) : Set (IrreducibleCloseds X) :=
  {C | topologicalKrullDim (C : Set X) = 1 ∧ (f '' (C : Set X)).Subsingleton}

/-- The native cardinal of the actual subtype; finite-count theorems below
supply finiteness explicitly before using this number. -/
def contractedCurveCount {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ :=
  Nat.card (contractedCurves f)

private theorem dimension_ne_one_of_subsingleton {A : Type u} [TopologicalSpace A]
    (C : Set A) (hC : C.Subsingleton) : topologicalKrullDim C ≠ 1 := by
  intro h
  let : Subsingleton C := ⟨fun x y ↦ Subtype.ext (hC x.property y.property)⟩
  have hle := topologicalKrullDim_zero_of_discreteTopology C
  rw [h] at hle
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hle

private theorem genericPoint_mem_targetIsomorphismLocus
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (hY : NormalStalks Y) :
    genericPoint Y ∈ f.targetIsomorphismLocus := by
  have hzero : Order.coheight (genericPoint Y) = 0 :=
    Order.coheight_eq_zero.mpr (fun z _ ↦ genericPoint_specializes z)
  obtain ⟨U, hηU, hU⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_coheight_le_one f hff hY
      (genericPoint Y) (by rw [hzero]; exact zero_le_one)
  exact f.le_targetIsomorphismLocus U hU hηU

private theorem contractedCurve_avoids_targetLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) (C : IrreducibleCloseds X)
    (hC : C ∈ contractedCurves f) :
    (C : Set X) ⊆ f ⁻¹' (f.targetIsomorphismLocus : Set Y)ᶜ := by
  intro x hx hxL
  let U := f.targetIsomorphismLocus
  let : IsIso (f ∣_ U) := f.isIso_restrict_targetIsomorphismLocus
  have hxU : f x ∈ U := hxL
  have hres (z : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) z) = f z.val :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ Y ↦ k z) (morphismRestrict_ι f U)
  have hss : (C : Set X).Subsingleton := by
    intro a ha b hb
    have hax : f a = f x := hC.2 ⟨a, ha, rfl⟩ ⟨x, hx, rfl⟩
    have hbx : f b = f x := hC.2 ⟨b, hb, rfl⟩ ⟨x, hx, rfl⟩
    have haU : a ∈ f ⁻¹ᵁ U := by
      change f a ∈ U
      rw [hax]
      exact hxU
    have hbU : b ∈ f ⁻¹ᵁ U := by
      change f b ∈ U
      rw [hbx]
      exact hxU
    have he : (f ∣_ U) ⟨a, haU⟩ = (f ∣_ U) ⟨b, hbU⟩ := by
      apply U.ι.injective
      exact (hres ⟨a, haU⟩).trans ((hax.trans hbx.symm).trans (hres ⟨b, hbU⟩).symm)
    exact congrArg Subtype.val ((f ∣_ U).injective he)
  exact dimension_ne_one_of_subsingleton (C : Set X) hss hC.1

/-- There are finitely many actual contracted curves. The target needs only
local Noetherianity and normality; no target dimension bound is needed here. -/
theorem finite_contractedCurves
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (hY : NormalStalks Y)
    (hdX : topologicalKrullDim X ≤ 2) : (contractedCurves f).Finite := by
  let E : Set X := f ⁻¹' (f.targetIsomorphismLocus : Set Y)ᶜ
  have hE : IsClosed E := f.targetIsomorphismLocus.isOpen.isClosed_compl.preimage f.continuous
  let : QuasiSober E := hE.isClosedEmbedding_subtypeVal.quasiSober
  have hη : genericPoint X ∉ E := by
    change f (genericPoint X) ∉ (f.targetIsomorphismLocus : Set Y)ᶜ
    rw [map_genericPoint_of_isDominant X f]
    exact fun hn ↦ hn (genericPoint_mem_targetIsomorphismLocus f hff hY)
  have hne : closure E ≠ Set.univ := by
    rw [hE.closure_eq]
    intro he
    exact hη (he ▸ Set.mem_univ _)
  let a : IrreducibleCloseds X ↪ X := (irreducibleSetEquivPoints (α := X)).toEquiv.toEmbedding
  apply ((NoetherianSpace.finite_coheight_one_of_closure_ne_univ hne).preimage_embedding a).subset
  intro C hC
  have hηC : a C ∈ (C : Set X) := (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  have hηE : a C ∈ E := contractedCurve_avoids_targetLocus f C hC hηC
  refine ⟨hηE, le_antisymm ?_ ?_⟩
  · apply coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two X hdX (a C)
    intro hc
    have hcl : closure ({a C} : Set X) = (C : Set X) := by
      change closure ({C.isIrreducible.genericPoint} : Set X) = (C : Set X)
      exact C.isIrreducible.closure_genericPoint C.isClosed
    have hsingle : (C : Set X) = {a C} := hcl.symm.trans hc.closure_eq
    exact dimension_ne_one_of_subsingleton (C : Set X)
      (by rw [hsingle]; exact Set.subsingleton_singleton) hC.1
  · apply Order.one_le_iff_ne_zero.mpr
    intro hz
    have hm := Order.coheight_eq_zero.mp hz
    have hback : a C ⤳ genericPoint X := hm (genericPoint_specializes (a C))
    have he : a C = genericPoint X :=
      (Specializes.antisymm hback (genericPoint_specializes (a C))).eq
    exact hη (he ▸ hηE)

/-- Original postcomposition retains every original contracted curve. -/
theorem contractedCurves_subset_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    contractedCurves f ⊆ contractedCurves (f ≫ g) := by
  intro C hC
  refine ⟨hC.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact congrArg g (hC.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-- Cardinal monotonicity retains explicit finiteness of the actual composite
curve set; the geometric theorem above supplies it in proper birational use. -/
theorem contractedCurveCount_le_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfin : (contractedCurves (f ≫ g)).Finite) :
    contractedCurveCount f ≤ contractedCurveCount (f ≫ g) := by
  simpa only [contractedCurveCount, Nat.card_coe_set_eq] using
    Set.ncard_le_ncard (contractedCurves_subset_comp f g) hfin

/-- A genuine extra original contracted curve gives strict decrease. -/
theorem contractedCurveCount_lt_comp_of_curve {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfin : (contractedCurves (f ≫ g)).Finite) (C : IrreducibleCloseds X)
    (hC : C ∈ contractedCurves (f ≫ g)) (hnot : C ∉ contractedCurves f) :
    contractedCurveCount f < contractedCurveCount (f ≫ g) := by
  have hs : contractedCurves f ⊂ contractedCurves (f ≫ g) := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨contractedCurves_subset_comp f g, ?_⟩
    intro he
    exact hnot (he.symm ▸ hC)
  simpa only [contractedCurveCount, Nat.card_coe_set_eq] using Set.ncard_lt_ncard hs hfin

private theorem dimension_closure_point_eq_one
    {X : Scheme.{u}} [IsIntegral X] (hdX : topologicalKrullDim X ≤ 2)
    (x : X) (hx : ¬ IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    topologicalKrullDim (closure ({x} : Set X)) = 1 := by
  let Z := closure ({x} : Set X)
  have havoid : Disjoint Z (genericPoints X) := by
    rw [genericPoints_eq_singleton, Set.disjoint_singleton_right]
    intro h
    exact hne (Specializes.antisymm (specializes_iff_mem_closure.mpr h)
      (genericPoint_specializes x)).eq
  have hle : topologicalKrullDim Z ≤ 1 :=
    topologicalKrullDim_closed_le_of_avoids_genericPoints Z isClosed_closure havoid 1 hdX
  have hn : ¬ Z ⊆ {x} := by
    intro h
    exact hx (isClosed_of_closure_subset h)
  obtain ⟨z, hz, hzne⟩ := Set.not_subset.mp hn
  have hzne' : z ≠ x := by simpa only [Set.mem_singleton_iff] using hzne
  let xZ : Z := ⟨x, subset_closure (Set.mem_singleton x)⟩
  let zZ : Z := ⟨z, hz⟩
  let : IrreducibleSpace Z :=
    isIrreducible_iff_irreducibleSpace.mp isIrreducible_singleton.closure
  let A : IrreducibleCloseds Z :=
    ⟨closure ({zZ} : Set Z), isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
  have hAB : A < B := by
    refine lt_of_le_not_ge (Set.subset_univ _) ?_
    intro h
    have hb : zZ ⤳ xZ := specializes_iff_mem_closure.mpr (h (Set.mem_univ xZ))
    exact hzne' (Specializes.antisymm (hb.map continuous_subtype_val)
      (specializes_iff_mem_closure.mpr hz)).eq
  have hbase : (1 : ℕ∞) ≤ Order.height A + 1 := by simp
  have hh : (1 : ℕ∞) ≤ Order.height B := hbase.trans (Order.height_add_one_le hAB)
  exact le_antisymm hle ((WithBot.coe_le_coe.mpr hh).trans (Order.height_le_krullDim B))

private theorem finite_of_closed_of_closed_singletons
    (X : Scheme.{u}) [NoetherianSpace X] {S : Set X} (hS : IsClosed S)
    (hpoints : ∀ x ∈ S, IsClosed ({x} : Set X)) : S.Finite := by
  obtain ⟨T, hTf, hTc, hTi, heq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have ht : ∀ C ∈ T, C.Finite := by
    intro C hC
    let x := (hTi C hC).genericPoint
    have hx := (hTi C hC).isGenericPoint_genericPoint (hTc C hC)
    have hxS : x ∈ S := by
      rw [heq]
      exact Set.mem_sUnion_of_mem hx.mem hC
    have hsingle : C = {x} := hx.symm.trans (hpoints x hxS).closure_eq
    rw [hsingle]
    exact Set.finite_singleton x
  rw [heq]
  exact hTf.sUnion ht

/-- If no actual curve is contracted, the original proper birational surface
morphism is an isomorphism. No source regularity or normality is needed. -/
theorem isIso_of_contractedCurves_eq_empty
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (hY : NormalStalks Y)
    (hdX : topologicalKrullDim X ≤ 2) (hdY : topologicalKrullDim Y ≤ 2)
    (hempty : contractedCurves f = ∅) : IsIso f := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  by_cases hy : y ∈ f.targetIsomorphismLocus
  · exact ⟨_, hy, f.isIso_restrict_targetIsomorphismLocus⟩
  have hyc := f.isClosed_singleton_of_not_mem_targetIsomorphismLocus hff hY hdY y hy
  have hfc : IsClosed (f ⁻¹' {y}) := hyc.preimage f.continuous
  have hpoints (x : X) (hx : x ∈ f ⁻¹' {y}) : IsClosed ({x} : Set X) := by
    by_contra hxc
    have hxne : x ≠ genericPoint X := by
      intro he
      have hfη : f (genericPoint X) = y := he ▸ hx
      rw [map_genericPoint_of_isDominant X f] at hfη
      exact hy (hfη ▸ genericPoint_mem_targetIsomorphismLocus f hff hY)
    let C : IrreducibleCloseds X :=
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
    have hsub : (C : Set X) ⊆ f ⁻¹' {y} :=
      closure_minimal (Set.singleton_subset_iff.mpr hx) hfc
    have hC : C ∈ contractedCurves f := by
      refine ⟨dimension_closure_point_eq_one hdX x hxc hxne, ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact (hsub ha).trans (hsub hb).symm
    rw [hempty] at hC
    exact Set.notMem_empty C hC
  have hf := finite_of_closed_of_closed_singletons X hfc hpoints
  exact exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton f hY hff y hf

/-- Zero is an isomorphism criterion only after the geometric finiteness proof,
so the infinite-subtype zero convention of Nat.card is never used. -/
theorem isIso_of_contractedCurveCount_eq_zero
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (hY : NormalStalks Y)
    (hdX : topologicalKrullDim X ≤ 2) (hdY : topologicalKrullDim Y ≤ 2)
    (hzero : contractedCurveCount f = 0) : IsIso f := by
  have hfin := finite_contractedCurves f hff hY hdX
  let : Finite (contractedCurves f) := hfin.to_subtype
  apply isIso_of_contractedCurves_eq_empty f hff hY hdX hdY
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro C hC
  let : Nonempty (contractedCurves f) := ⟨⟨C, hC⟩⟩
  have hp : 0 < contractedCurveCount f := Nat.card_pos
  rw [hzero] at hp
  exact (Nat.lt_irrefl 0) hp

/-- The original image of an isomorphism cannot contract an actual curve. -/
theorem contractedCurves_eq_empty_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    contractedCurves f = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro C hC
  apply dimension_ne_one_of_subsingleton (C : Set X) _ hC.1
  intro a ha b hb
  exact f.injective (hC.2 ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)

private theorem image_generic_closure {D B : Scheme.{u}} [IsIntegral D]
    (j : D ⟶ B) [IsClosedImmersion j] :
    closure ({j (genericPoint D)} : Set B) = Set.range j := by
  rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ]

private theorem image_not_subsingleton_of_dimension_one
    {D B : Scheme.{u}} (j : D ⟶ B) [IsClosedImmersion j]
    (hdD : topologicalKrullDim D = 1) : ¬ (Set.range j).Subsingleton := by
  intro hss
  let : Subsingleton D := ⟨fun a b ↦ j.injective (hss ⟨a, rfl⟩ ⟨b, rfl⟩)⟩
  have hle := topologicalKrullDim_zero_of_discreteTopology D
  rw [hdD] at hle
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hle

/-- The closure of the original inverse-image generic point of an actual
closed curve dominates that entire curve. It is not assumed isomorphic to it. -/
theorem exists_contractedCurve_comp_not_of_closed_curve
    {X B Y D : Scheme.{u}} [IsIntegral X] [IsIntegral B] [IsIntegral D]
    [IsLocallyNoetherian B] (g : X ⟶ B) [IsProper g] [IsDominant g]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) (hB : NormalStalks B)
    (hdX : topologicalKrullDim X ≤ 2) (hdB : topologicalKrullDim B ≤ 2)
    (p : B ⟶ Y) (j : D ⟶ B) [IsClosedImmersion j]
    (hdD : topologicalKrullDim D = 1) (hη : genericPoint B ∉ Set.range j)
    (hp : (p '' Set.range j).Subsingleton) :
    ∃ C : IrreducibleCloseds X, g '' (C : Set X) = Set.range j ∧
      C ∈ contractedCurves (g ≫ p) ∧ C ∉ contractedCurves g := by
  let η := j (genericPoint D)
  have hηclosure : closure ({η} : Set B) = Set.range j := image_generic_closure j
  have hηnc : ¬ IsClosed ({η} : Set B) := by
    intro hc
    apply image_not_subsingleton_of_dimension_one j hdD
    rw [← hηclosure, hc.closure_eq]
    exact Set.subsingleton_singleton
  have hcodim := coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two B hdB η hηnc
  obtain ⟨U, hηU, hU⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_coheight_le_one g hff hB η hcodim
  let : IsIso (g ∣_ U) := hU
  obtain ⟨xU, hxU⟩ := (g ∣_ U).surjective (⟨η, hηU⟩ : U.toScheme)
  let x : X := xU.val
  have hgx : g x = η := by
    have hc := congrArg (fun k : (g ⁻¹ᵁ U).toScheme ⟶ B ↦ k xU) (morphismRestrict_ι g U)
    change U.ι ((g ∣_ U) xU) = g x at hc
    exact hc.symm.trans (congrArg (fun z : U.toScheme ↦ U.ι z) hxU)
  let C : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  have hsub : (C : Set X) ⊆ g ⁻¹' Set.range j :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨genericPoint D, hgx.symm⟩)
      (j.isClosedEmbedding.isClosed_range.preimage g.continuous)
  have hηimage : η ∈ g '' (C : Set X) := ⟨x, subset_closure (Set.mem_singleton x), hgx⟩
  have himage : g '' (C : Set X) = Set.range j := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hsub hz
    · rw [← hηclosure]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηimage) (g.isClosedMap _ C.isClosed)
  have hnot : ¬ (g '' (C : Set X)).Subsingleton := by
    rw [himage]
    exact image_not_subsingleton_of_dimension_one j hdD
  have hxnc : ¬ IsClosed ({x} : Set X) := by
    intro hc
    apply hnot
    change (g '' closure ({x} : Set X)).Subsingleton
    rw [hc.closure_eq]
    exact Set.subsingleton_singleton.image g
  have hxne : x ≠ genericPoint X := by
    intro he
    have hgen : g x = genericPoint B := by
      rw [he, map_genericPoint_of_isDominant X g]
    exact hη ((hgx.symm.trans hgen) ▸ (show η ∈ Set.range j from ⟨genericPoint D, rfl⟩))
  have hdim : topologicalKrullDim (C : Set X) = 1 :=
    dimension_closure_point_eq_one hdX x hxnc hxne
  refine ⟨C, himage, ⟨hdim, ?_⟩, fun hC ↦ hnot hC.2⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact hp ⟨g a, hsub ha, rfl⟩ ⟨g b, hsub hb, rfl⟩

private theorem ne_generic_of_stalk_dimension_two
    {Y : Scheme.{u}} [IsIntegral Y] (y : Y)
    (hd : ringKrullDim (Y.presheaf.stalk y) = 2) : y ≠ genericPoint Y := by
  intro h
  subst y
  change ringKrullDim Y.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

private theorem normalStalks_of_regular {Y : Scheme.{u}} (hY : RegularStalks Y) :
    NormalStalks Y := by
  intro y
  let : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

/-- Factoring through the actual blowup of an original closed regular
surface point strictly decreases the proved finite contracted-curve count.
The actual field-map premise uses the integral blowup proved from that point. -/
theorem contractedCurveCount_lt_pointBlowup
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    [IsLocallyNoetherian Y]
    (hY : RegularStalks Y) (hdX : topologicalKrullDim X ≤ 2)
    (hdY : topologicalKrullDim Y ≤ 2) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdy : ringKrullDim (Y.presheaf.stalk y) = 2)
    (g : X ⟶ (Blowup.blowupDatum (Y.fromSpecResidueField y).ker).Y) [IsProper g] [IsDominant g]
    (hff : let : IsIntegral (Blowup.blowupDatum (Y.fromSpecResidueField y).ker).Y :=
        Blowup.pointBlowup_isIntegral Y y hy (by
          intro he
          have hd := hdy
          rw [he] at hd
          change ringKrullDim Y.functionField = 2 at hd
          rw [ringKrullDim_eq_zero_of_field] at hd
          norm_num at hd)
      IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    contractedCurveCount g <
      contractedCurveCount (g ≫ (Blowup.blowupDatum (Y.fromSpecResidueField y).ker).map) := by
  let B := Blowup.blowupDatum (Y.fromSpecResidueField y).ker
  have hne := ne_generic_of_stalk_dimension_two y hdy
  let : IsIntegral B.Y := Blowup.pointBlowup_isIntegral Y y hy hne
  let : IsDominant B.map := Blowup.pointBlowup_isDominant Y y hy hne
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  have hffg : IsIso (CommRingCat.ofHom (functionFieldMap g)) := hff
  let : IsIso (CommRingCat.ofHom (functionFieldMap g)) := hffg
  let : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
    B.functionFieldMap_isIso (Blowup.genericPoint_not_mem_pointCentre y hy hne)
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (g ≫ B.map))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  have hregB := Blowup.RegularPoint.regularStalks_pointBlowup Y hY y hy hdy
  have hdimY : ∀ z : Y, ringKrullDim (Y.presheaf.stalk z) ≤ 2 := by
    rw [topologicalKrullDim_eq_iSup_stalk] at hdY
    intro z
    exact (le_iSup (fun z : Y ↦ ringKrullDim (Y.presheaf.stalk z)) z).trans hdY
  have hdB : topologicalKrullDim B.Y ≤ 2 := by
    rw [topologicalKrullDim_eq_iSup_stalk]
    exact iSup_le (Blowup.pointBlowup_stalk_dimension_le_two hY hdimY y hy hdy)
  let : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
  let D := Blowup.RegularPoint.pointExceptionalFibre Y y
  let j : D ⟶ B.Y := Blowup.RegularPoint.pointExceptionalι Y y
  let e : D ≅ ProjectiveLine.projectiveP1 (ResidueField (Y.presheaf.stalk y)) :=
    (Over.forget _).mapIso (Blowup.RegularPoint.pointExceptionalOverIsoProjectiveP1 Y y hy hdy)
  let : IsIntegral D := IsIntegral.of_isIso e.inv
  let : IsClosedImmersion j := Blowup.RegularPoint.pointExceptionalι_isClosedImmersion Y y hy
  let e' := e ≪≫
    (PinchedLine.ProjectiveComparison.lineIsoP1 (ResidueField (Y.presheaf.stalk y))).symm
  have hdD : topologicalKrullDim D = 1 := by
    calc
      _ = topologicalKrullDim (PinchedLine.lineGluing (ResidueField (Y.presheaf.stalk y))) :=
        IsHomeomorph.topologicalKrullDim_eq e'.hom e'.hom.homeomorph.isHomeomorph
      _ = _ := PinchedLine.line_dimension_eq_one _
  have hjy (d : D) : B.map (j d) = y := by
    have hh := congrArg (fun k : D ⟶ Y ↦ k d)
      (pullback.condition (f := B.map) (g := Y.fromSpecResidueField y))
    change B.map (j d) = Y.fromSpecResidueField y
      ((pullback.snd B.map (Y.fromSpecResidueField y)) d) at hh
    exact hh.trans (fromSpecResidueField_apply y _)
  have hη : genericPoint B.Y ∉ Set.range j := by
    rintro ⟨d, hd⟩
    apply hne
    have hgen := map_genericPoint_of_isDominant B.Y B.map
    exact (hjy d).symm.trans ((congrArg B.map hd).trans hgen)
  have hp : (B.map '' Set.range j).Subsingleton := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩ _ ⟨_, ⟨e, rfl⟩, rfl⟩
    exact (hjy d).trans (hjy e).symm
  obtain ⟨C, _, hC, hnot⟩ := exists_contractedCurve_comp_not_of_closed_curve
    g hffg (normalStalks_of_regular hregB) hdX hdB B.map j hdD hη hp
  exact contractedCurveCount_lt_comp_of_curve g B.map
    (finite_contractedCurves (g ≫ B.map) hcomp (normalStalks_of_regular hY) hdX) C hC hnot

end AlgebraicGeometry.Scheme
