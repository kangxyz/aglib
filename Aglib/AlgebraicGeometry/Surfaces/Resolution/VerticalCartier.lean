/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Product
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.SectionFibres
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ConnectedFibres
public import Aglib.AlgebraicGeometry.Morphisms.Proper.QuasiFinite
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GlobalSections
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.RingTheory.Ideal.HeightOne
public import Aglib.RingTheory.IntegralClosure.HeightOneLocalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Data.Finset.Max

/-!
# Nontrivial conormal of a vertical Cartier divisor

A nonempty effective Cartier divisor supported on the closed fibre of a
normal proper birational modification of a two-dimensional normal
Noetherian local domain has nontrivial conormal. The conclusion concerns
the original closed immersion and its actual pulled ideal module.

The common base function from Stacks 0AX9 retains the original function-field
and base-to-stalk maps. Actual component generic-point valuations and
height-one membership construct a section of a positive ideal power.
Its restriction to a reduced component is nonzero and is not invertible
at a chosen closed point. Proper integral global functions then obstruct
a trivialization, giving the conormal conclusion of Stacks 0AXA without
a degree, regularity, excellence, or resolution hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.VerticalCartier

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The original coefficient action on the function field of its affine spectrum. -/
local instance functionFieldSpecAlgebra [IsDomain A] : Algebra A (Spec (.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)

local instance [IsDomain A] : IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (.of A)

/-- The original base-ring map into the actual point stalk. -/
def baseStalkMap (q : X ⟶ Spec (.of A)) (x : X) : A →+* X.presheaf.stalk x :=
  (StructureSheaf.toStalk A (q x) ≫ q.stalkMap x).hom

private theorem affine_scalar_stalk_to_functionField [IsDomain A]
    (x : Spec (.of A)) (a : A) :
    algebraMap ((Spec (.of A)).presheaf.stalk x) (Spec (.of A)).functionField
        (StructureSheaf.toStalk A x a) =
      algebraMap A (Spec (.of A)).functionField a := by
  change (StructureSheaf.toStalk A x ≫
    (Spec (.of A)).presheaf.stalkSpecializes
      ((genericPoint_spec (Spec (.of A))).specializes (Set.mem_univ x))) a =
    StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a
  exact congrArg (fun f : CommRingCat.of A ⟶ (Spec (.of A)).functionField => f a)
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec (.of A))).specializes (Set.mem_univ x)))

/-- Localization of the original scalar map agrees with the original
birational function-field map. -/
theorem baseStalkMap_functionField [IsDomain A] [IsIntegral X]
    (q : X ⟶ Spec (.of A)) [IsDominant q] (x : X) (a : A) :
    algebraMap (X.presheaf.stalk x) X.functionField (baseStalkMap q x a) =
      functionFieldMap q (algebraMap A (Spec (.of A)).functionField a) := by
  rw [← affine_scalar_stalk_to_functionField (q x) a]
  exact (functionFieldMap_stalk q x (StructureSheaf.toStalk A (q x) a)).symm

private theorem exists_nonzero_numerator [IsDomain A] [IsIntegral X]
    (q : X ⟶ Spec (.of A)) [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (x : X) (g : X.presheaf.stalk x) (hg : g ≠ 0) :
    ∃ a b : A, a ≠ 0 ∧ b ≠ 0 ∧ baseStalkMap q x a = g * baseStalkMap q x b := by
  let := hff
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (functionFieldMap q))).surjective
      (algebraMap (X.presheaf.stalk x) X.functionField g)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A z
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbF : functionFieldMap q (algebraMap A (Spec (.of A)).functionField b) ≠ 0 := by
    apply (map_ne_zero (functionFieldMap q)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective A (Spec (.of A)).functionField)).mpr hb0
  have hf : functionFieldMap q (algebraMap A (Spec (.of A)).functionField a) /
      functionFieldMap q (algebraMap A (Spec (.of A)).functionField b) =
        algebraMap (X.presheaf.stalk x) X.functionField g := by
    rw [← map_div₀, hab]
    exact hz
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, map_zero, zero_div] at hf
    apply hg
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      (hf.symm.trans (map_zero (algebraMap (X.presheaf.stalk x) X.functionField)).symm)
  refine ⟨a, b, ha0, hb0, ?_⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, baseStalkMap_functionField, baseStalkMap_functionField]
  exact (div_eq_iff hbF).mp hf

private theorem exists_nonunit_lift {C : Scheme.{u}}
    (j : C ⟶ X) [IsClosedImmersion j] (x : C)
    (hx : ¬IsField (C.presheaf.stalk x)) :
    ∃ g : X.presheaf.stalk (j x),
      g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j x)) ∧
        j.stalkMap x g ≠ 0 := by
  have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hx
  obtain ⟨z, hz, hz0⟩ := (IsLocalRing.maximalIdeal (C.presheaf.stalk x)).ne_bot_iff.mp hm
  obtain ⟨g, hg⟩ := j.stalkMap_surjective x z
  refine ⟨g, ?_, hg.symm ▸ hz0⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
  intro hunit
  exact hz (hg ▸ hunit.map (j.stalkMap x).hom)

/-- At any finite nonempty family of actual nonfield closed-subscheme
stalks, one nonzero function in the original local base maximal ideal has
all the numerator factorizations from Stacks 0AX9. The points and their
original closed-subscheme maps are retained; no common function is assumed.
Component-isolating point selection is not a premise hidden in this statement. -/
theorem exists_base_function_factor_at_points [IsDomain A] [IsLocalRing A]
    [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    {ι : Type u} [Finite ι] [Nonempty ι]
    (C : ι → Scheme.{u}) (j : ∀ t, C t ⟶ X) [∀ t, IsClosedImmersion (j t)]
    (x : ∀ t, C t) (hx : ∀ t, ¬IsField ((C t).presheaf.stalk (x t))) :
    ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧
      ∀ t, ∃ g r : X.presheaf.stalk (j t (x t)),
        g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j t (x t))) ∧
        (j t).stalkMap (x t) g ≠ 0 ∧ baseStalkMap q (j t (x t)) f = g * r := by
  classical
  let := Fintype.ofFinite ι
  choose g hgm hgC using fun t => exists_nonunit_lift (j t) (x t) (hx t)
  have hg0 (t : ι) : g t ≠ 0 := by
    intro h
    apply hgC t
    rw [h]
    exact map_zero ((j t).stalkMap (x t)).hom
  choose a b ha hb hab using fun t => exists_nonzero_numerator q hff _ (g t) (hg0 t)
  have ham (t : ι) : a t ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hmem : baseStalkMap q (j t (x t)) (a t) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (j t (x t))) := by
      rw [hab t]
      exact Ideal.mul_mem_right _ _ (hgm t)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact hmem (hunit.map (baseStalkMap q (j t (x t))))
  let f : A := ∏ t, a t
  have hf (t : ι) : f = a t * ∏ s ∈ Finset.univ.erase t, a s := by
    exact (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ t)).symm
  refine ⟨f, Finset.prod_ne_zero_iff.mpr (fun t _ => ha t), ?_, ?_⟩
  · let t : ι := Classical.choice inferInstance
    rw [hf t]
    exact Ideal.mul_mem_right _ _ (ham t)
  · intro t
    let α := baseStalkMap q (j t (x t))
    refine ⟨g t, α (b t) * α (∏ s ∈ Finset.univ.erase t, a s), hgm t, hgC t, ?_⟩
    rw [hf t, map_mul, hab t, mul_assoc]

/-- A minimal point of the original Cartier subscheme has ambient coheight
one, even if that subscheme is not reduced. This is the local principal
ideal theorem applied to its original closed-immersion stalk kernel. -/
theorem coheight_eq_one_of_minimal_cartier_point
    {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (z : Z) (hz : Order.coheight z = 0) : Order.coheight (i z) = 1 := by
  let R := X.presheaf.stalk (i z)
  let S := Z.presheaf.stalk z
  let φ : R →+* S := (i.stalkMap z).hom
  let : Ring.KrullDimLE 0 S := krullDimLE_of_coheight_le hz.le
  have hmS : IsLocalRing.maximalIdeal S ∈ (⊥ : Ideal S).minimalPrimes :=
    Ring.KrullDimLE.mem_minimalPrimes_iff.mpr ⟨inferInstance, bot_le⟩
  have hmR : IsLocalRing.maximalIdeal R ∈ (RingHom.ker φ).minimalPrimes := by
    have ht : (IsLocalRing.maximalIdeal S).comap φ ∈ (Ideal.comap φ ⊥).minimalPrimes :=
      Ideal.minimalPrimes_comap_of_surjective (i.stalkMap_surjective z) hmS
    rw [IsLocalRing.maximalIdeal_comap, ← RingHom.ker_eq_comap_bot] at ht
    exact ht
  obtain ⟨U, hU, hxU, a, ha, hker⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI (i z)
  let : Nonempty U := ⟨⟨i z, hxU⟩⟩
  let r : R := X.presheaf.germ U (i z) hxU a
  have hk : RingHom.ker φ = Ideal.span {r} := by
    rw [ker_stalkMap_eq_map_ker_app i U hU z hxU, hker]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have ha0 : a ≠ 0 := by
    intro h
    exact zero_ne_one (ha (by simp [h] : a • (0 : Γ(X, U)) = a • (1 : Γ(X, U))))
  have hr0 : r ≠ 0 := by
    intro h
    exact ha0 (germ_injective_of_isIntegral X (i z) hxU
      (h.trans (map_zero (X.presheaf.germ U (i z) hxU).hom).symm))
  have hm : (IsLocalRing.maximalIdeal R).height = 1 :=
    Ideal.minimalPrime_height_one (mem_nonZeroDivisors_iff_ne_zero.mpr hr0) (hk ▸ hmR)
  have hd : ringKrullDim R = 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hm
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd


private theorem isOpen_singleton_of_closed_no_generalizations
    (Y : Scheme.{u}) [IsNoetherian Y] (x : Y)
    (hx : IsClosed ({x} : Set Y))
    (hgen : ∀ y : Y, y ⤳ x → y = x) : IsOpen ({x} : Set Y) := by
  let U : Y.Opens := Y.irreducibleComponentOpen {x}
  have hcomponent (Z : Set Y) (hZ : Z ∈ irreducibleComponents Y) (hxZ : x ∈ Z) :
      Z = {x} := by
    let z := hZ.1.genericPoint
    have hz : IsGenericPoint z Z :=
      hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have he := hgen z (hz.specializes hxZ)
    rw [← hz.def, he, hx.closure_eq]
  have hxU : x ∈ U := by
    change x ∉ ⋃₀ (irreducibleComponents Y \ {{x}})
    rintro ⟨Z, ⟨hZ, hne⟩, hxZ⟩
    exact hne (hcomponent Z hZ hxZ)
  have hU : (U : Set Y) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨Z, hZ, hyZ⟩ := Set.mem_sUnion.mp
        ((sUnion_irreducibleComponents (X := Y)).symm ▸ Set.mem_univ y)
      by_cases hZx : Z = {x}
      · exact hZx ▸ hyZ
      · exact False.elim (hy ⟨Z, ⟨hZ, hZx⟩, hyZ⟩)
    · exact Set.singleton_subset_iff.mpr hxU
  exact hU ▸ U.isOpen

private theorem generic_of_strict_generalization_of_coheight_one
    {Y : Scheme.{u}} [IsIntegral Y] {x y : Y} (hx : Order.coheight x = 1)
    (hy : y ⤳ x) (hne : y ≠ x) : y = genericPoint Y := by
  have hxy : x < y := lt_iff_le_not_ge.mpr
    ⟨hy, fun h => hne (Specializes.antisymm hy h).eq⟩
  have hh : Order.coheight y + 1 ≤ 1 := by
    simpa only [hx] using Order.coheight_add_one_le hxy
  have hy0 : Order.coheight y = 0 := by
    apply le_antisymm _ bot_le
    exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hh
  have hm := Order.coheight_eq_zero.mp hy0
  apply (Specializes.antisymm _ ((genericPoint_spec Y).specializes (Set.mem_univ y))).eq
  exact hm ((genericPoint_spec Y).specializes (Set.mem_univ y))

/-- A closed source point of coheight one is isolated in a nongeneric
fibre of the original dominant morphism. -/
private theorem quasiFiniteAt_of_closed_coheight_one
    {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
    (q : Y ⟶ T) [IsProper q] [IsDominant q]
    (x : Y) (hx : IsClosed ({x} : Set Y)) (hd : Order.coheight x = 1)
    (hqx : q x ≠ genericPoint T) : q.QuasiFiniteAt x := by
  let F := q.fiber (q x)
  let p := q.asFiber x
  let : IsProper (q.fiberToSpecResidueField (q x)) := by
    change IsProper (pullback.snd q (T.fromSpecResidueField (q x)))
    infer_instance
  let : IsLocallyNoetherian F :=
    LocallyOfFiniteType.isLocallyNoetherian (q.fiberToSpecResidueField (q x))
  let : CompactSpace F := QuasiCompact.compactSpace_of_compactSpace
    (q.fiberToSpecResidueField (q x))
  let : IsNoetherian F := ⟨⟩
  have hp : IsClosed ({p} : Set F) := by
    convert hx.preimage (q.fiberι (q x)).continuous using 1
    ext z
    change z = p ↔ q.fiberι (q x) z = x
    constructor
    · intro h
      subst z
      exact q.fiberι_asFiber x
    · intro h
      exact (q.fiberι (q x)).isEmbedding.injective (h.trans (q.fiberι_asFiber x).symm)
  apply (Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber (f := q)).mpr
  apply isOpen_singleton_of_closed_no_generalizations F p hp
  intro z hz
  apply (q.fiberι (q x)).isEmbedding.injective
  rw [q.fiberι_asFiber]
  by_contra hne
  have hspec : q.fiberι (q x) z ⤳ x := by
    exact (hz.map (q.fiberι (q x)).continuous).trans
      (specializes_of_eq (q.fiberι_asFiber x))
  have he := generic_of_strict_generalization_of_coheight_one hd hspec hne
  have hqz : q (q.fiberι (q x) z) = q x :=
    (q.fiberHomeo (q x) z).property
  rw [he, map_genericPoint_of_isDominant Y q] at hqz
  exact hqx hqz.symm

private theorem finite_fibre_of_connected_quasiFiniteAt
    {Y T : Scheme.{u}} (q : Y ⟶ T) [LocallyOfFiniteType q]
    [GeometricallyConnected q] (x : Y) (hx : q.QuasiFiniteAt x) :
    (q ⁻¹' {q x}).Finite := by
  have hall : ({q.asFiber x} : Set (q.fiber (q x))) = Set.univ :=
    hx.isClopen_singleton_asFiber.eq_univ ⟨q.asFiber x, rfl⟩
  apply (Set.finite_singleton x).subset
  intro y hy
  let z := (q.fiberHomeo (q x)).symm ⟨y, hy⟩
  have hz : z = q.asFiber x := by
    apply Set.mem_singleton_iff.mp
    rw [hall]
    exact Set.mem_univ _
  calc
    y = q.fiberι (q x) z := (q.fiberι_fiberHomeo_symm (q x) ⟨y, hy⟩).symm
    _ = x := by rw [hz, q.fiberι_asFiber]

/-- A closed source point of coheight one in a proper birational map onto
a normal target has an actual target isomorphism neighborhood, provided
its image is not generic. This rules out isolated vertical Cartier
components without an ambient dimension bound on the source. -/
theorem exists_isIso_restrict_of_closed_coheight_one
    {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T]
    (q : Y ⟶ T) [IsProper q] [IsDominant q] (hT : NormalStalks T)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (x : Y) (hx : IsClosed ({x} : Set Y)) (hd : Order.coheight x = 1)
    (hqx : q x ≠ genericPoint T) :
    ∃ U : T.Opens, q x ∈ U ∧ IsIso (q ∣_ U) := by
  let : GeometricallyConnected q := geometricallyConnected_of_isProper_birational q hT hff
  exact exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton q hT hff
    (q x) (finite_fibre_of_connected_quasiFiniteAt q x
      (quasiFiniteAt_of_closed_coheight_one q x hx hd hqx))

private theorem closedPoint_ne_generic_of_dimension_two
    [IsDomain A] [IsLocalRing A] (hdim : ringKrullDim A = 2) :
    (IsLocalRing.closedPoint A : Spec (.of A)) ≠ genericPoint (Spec (.of A)) := by
  intro he
  have hf : IsField ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
    he.symm ▸ Field.toIsField (Spec (.of A)).functionField
  have hA : IsField A := (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.isField hf
  have hh := ringKrullDim_eq_zero_of_isField hA
  rw [hdim] at hh
  norm_num at hh

private theorem ringKrullDim_closed_stalk [IsLocalRing A] :
    ringKrullDim ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) =
      ringKrullDim A :=
  (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv.ringKrullDim

private theorem coheight_eq_of_restrict_isIso {Y T : Scheme.{u}}
    (q : Y ⟶ T) (U : T.Opens) [IsIso (q ∣_ U)] (x : Y) (hx : q x ∈ U) :
    Order.coheight (q x) = Order.coheight x := by
  let z : (q ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have hl := coheight_eq_of_isOpenImmersion (x := z) ((q ∣_ U) ≫ U.ι)
  have hr := coheight_eq_of_isOpenImmersion (x := z) (q ⁻¹ᵁ U).ι
  have hp : ((q ∣_ U) ≫ U.ι) z = q x := by
    rw [morphismRestrict_ι, Hom.comp_apply]
    rfl
  change Order.coheight x = Order.coheight z at hr
  exact ((congrArg (fun y : T => Order.coheight y) hp).symm.trans hl).trans hr.symm

/-- A vertical coheight-one point over a two-dimensional local normal
base is not closed. The original closed fibre is used, and no global
dimension or regularity condition on the modification is assumed. -/
theorem not_isClosed_of_coheight_one_over_closedPoint
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (hdim : ringKrullDim A = 2) (x : X) (hx : Order.coheight x = 1)
    (hqx : q x = IsLocalRing.closedPoint A) : ¬IsClosed ({x} : Set X) := by
  have hbase : NormalStalks (Spec (.of A)) :=
    fun y => isIntegrallyClosed_and_isDomain_stalk_Spec A y |>.symm
  have hng : q x ≠ genericPoint (Spec (.of A)) :=
    fun h => closedPoint_ne_generic_of_dimension_two hdim (hqx.symm.trans h)
  intro hc
  obtain ⟨U, hU, hu⟩ := exists_isIso_restrict_of_closed_coheight_one q hbase hff x hc hx hng
  let := hu
  have he : Order.coheight (q x) = 1 := (coheight_eq_of_restrict_isIso q U x hU).trans hx
  have hs : ringKrullDim ((Spec (.of A)).presheaf.stalk (q x)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast he
  have hsA : ringKrullDim ((Spec (.of A)).presheaf.stalk (q x)) = ringKrullDim A := by
    rw [hqx]
    exact ringKrullDim_closed_stalk
  have hh := hsA.symm.trans hs
  rw [hdim] at hh
  norm_num at hh

/-- The original base scalar map into any actual stalk is injective for
an integral dominant scheme over the original domain. -/
theorem baseStalkMap_injective [IsDomain A] [IsIntegral X]
    (q : X ⟶ Spec (.of A)) [IsDominant q] (x : X) :
    Function.Injective (baseStalkMap q x) := by
  intro a b hab
  apply IsFractionRing.injective A (Spec (.of A)).functionField
  apply (functionFieldMap q).injective
  rw [← baseStalkMap_functionField q x a, ← baseStalkMap_functionField q x b, hab]

private theorem not_isField_stalk_of_closed_of_generic_not_closed
    (C : Scheme.{u}) [IsIntegral C] (x : C) (hx : IsClosed ({x} : Set C))
    (hgen : ¬IsClosed ({genericPoint C} : Set C)) : ¬IsField (C.presheaf.stalk x) := by
  intro hf
  have hh := ringKrullDim_eq_zero_of_isField hf
  rw [ringKrullDim_stalk_eq_coheight] at hh
  have hco : Order.coheight x = 0 := by exact_mod_cast hh
  have hmax := Order.coheight_eq_zero.mp hco
  have hxg : x = genericPoint C :=
    (Specializes.antisymm (hmax le_top) (genericPoint_specializes x)).eq
  exact hgen (hxg ▸ hx)

/-- A nonempty actual open of an integral finite-type field scheme has
an actual closed nonfield-stalk point if its generic point is not closed.
The selected point is not assumed rational over the field. -/
theorem exists_closed_nonfield_point_in_open
    {k : Type u} [Field k] (C : OverField.FScheme k)
    [IsIntegral C.left] [LocallyOfFiniteType C.hom]
    (U : C.left.Opens) (hU : (U : Set C.left).Nonempty)
    (hgen : ¬IsClosed ({genericPoint C.left} : Set C.left)) :
    ∃ x ∈ U, IsClosed ({x} : Set C.left) ∧ ¬IsField (C.left.presheaf.stalk x) := by
  let : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  obtain ⟨x, hxU, hx⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  exact ⟨x, hxU, hx, not_isField_stalk_of_closed_of_generic_not_closed C.left x hx hgen⟩


private theorem unit_endomorphism_isIso_of_ne_zero
    {k : Type u} [Field k] (C : OverField.FScheme k)
    [IsProper C.hom] [IsIntegral C.left]
    (ν : SheafOfModules.unit C.left.ringCatSheaf ⟶
      SheafOfModules.unit C.left.ringCatSheaf) (hν : ν ≠ 0) : IsIso ν := by
  let : Field Γ(C.left, ⊤) := (globalSections_isField C).toField
  let a : Γ(C.left, ⊤) := ν.val.app (op ⊤) (1 : Γ(C.left, ⊤))
  have ha : a ≠ 0 := by
    intro hz
    apply hν
    apply (Modules.unitHomGlobalSectionsAddEquiv C.left
      (SheafOfModules.unit C.left.ringCatSheaf)).injective
    change a = (Modules.unitHomGlobalSectionsAddEquiv C.left
      (SheafOfModules.unit C.left.ringCatSheaf)) 0
    exact hz.trans (map_zero (Modules.unitHomGlobalSectionsAddEquiv C.left
      (SheafOfModules.unit C.left.ringCatSheaf))).symm
  let a' : Γ(C.left, ⊤)ˣ := Units.mk0 a ha
  have he : ν = (Modules.Invertible.ScalarAutomorphisms.scalarIso C.left
      (SheafOfModules.unit C.left.ringCatSheaf) a').hom :=
    Modules.Invertible.ScalarAutomorphisms.unit_hom_eq_scalar C.left ν
  exact he ▸ inferInstance

/-- A nonzero actual section with an actual zero residue fibre prevents
triviality on any proper integral scheme over the specified field.
No regularity, dimension, geometric integrality, or perfectness is needed. -/
theorem nontrivial_of_nonzero_section_with_zero_fibre
    {k : Type u} [Field k] (C : OverField.FScheme k)
    [IsProper C.hom] [IsIntegral C.left] (M : C.left.Modules)
    (s : SheafOfModules.unit C.left.ringCatSheaf ⟶ M) (hs : s ≠ 0)
    (x : C.left) (hx : (Modules.pullback (C.left.fromSpecResidueField x)).map s = 0) :
    ¬Nonempty (M ≅ SheafOfModules.unit C.left.ringCatSheaf) := by
  rintro ⟨e⟩
  have hse : s ≫ e.hom ≠ 0 := by
    intro h
    exact hs ((cancel_mono e.hom).mp (h.trans (zero_comp).symm))
  let : IsIso (s ≫ e.hom) := unit_endomorphism_isIso_of_ne_zero C (s ≫ e.hom) hse
  let : IsIso s := (isIso_comp_right_iff s e.hom).mp inferInstance
  let t := C.left.fromSpecResidueField x
  let u := Modules.Invertible.PowerPullback.freeUnitIso C.left
  let L := Modules.Invertible.pullbackLineBundle t (Modules.Invertible.trivialLineBundle C.left)
  have hn := Modules.Invertible.lineBundleMap_ne_zero_of_mono
    (Spec (C.left.residueField x)) L ((Modules.pullback t).map (u.hom ≫ s))
  apply hn
  rw [Functor.map_comp, hx, comp_zero]

variable {Z : Scheme.{u}}

/-- The original closed image of one irreducible component of the Cartier
subscheme. This uses its actual closed immersion, not a chosen replacement. -/
def componentClosed (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : Closeds X :=
  ⟨i '' c.val, i.isClosedMap c.val (isClosed_of_mem_irreducibleComponents c.val c.property)⟩

/-- The native reduced closed ideal of the original component image. -/
def componentIdeal (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : X.IdealSheafData :=
  IdealSheafData.vanishingIdeal (componentClosed i c)

/-- The native reduced subscheme of the original component image. -/
abbrev componentScheme (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : Scheme.{u} := (componentIdeal i c).subscheme

/-- Its original closed immersion into the modification. -/
def componentι (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : componentScheme i c ⟶ X :=
  (componentIdeal i c).subschemeι

instance componentι_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : IsClosedImmersion (componentι i c) :=
  inferInstanceAs (IsClosedImmersion (componentIdeal i c).subschemeι)

@[simp]
theorem range_componentι (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : Set.range (componentι i c) = i '' c.val := by
  exact (IdealSheafData.range_subschemeι (componentIdeal i c)).trans
    (IdealSheafData.coe_support_vanishingIdeal (componentClosed i c))

instance componentScheme_isIntegral (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : IsIntegral (componentScheme i c) := by
  have hs : (componentIdeal i c).support = componentClosed i c := by
    apply Closeds.ext
    exact IdealSheafData.coe_support_vanishingIdeal (componentClosed i c)
  have hrad : (componentIdeal i c).radical = componentIdeal i c := by
    rw [← IdealSheafData.vanishingIdeal_support, hs]
    rfl
  let : IsReduced (componentScheme i c) :=
    IdealSheafData.subscheme_reduced_of_radical (componentIdeal i c) hrad
  have hirr : IsIrreducible ((componentIdeal i c).support : Set X) := by
    rw [hs]
    exact c.property.1.image i i.continuous.continuousOn
  let : IrreducibleSpace (componentScheme i c) := Subtype.irreducibleSpace hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The original reduced component factors through the original Cartier
subscheme by the native reduced-source kernel comparison. -/
def componentToDivisor (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : componentScheme i c ⟶ Z :=
  liftReducedToClosed i (componentι i c) (by
    rw [range_componentι]
    exact Set.image_subset_range _ _)

@[reassoc (attr := simp)]
theorem componentToDivisor_fac (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) : componentToDivisor i c ≫ i = componentι i c :=
  liftReducedToClosed_fac _ _ _

private theorem component_generic_coheight_zero (c : irreducibleComponents Z) :
    Order.coheight c.property.1.genericPoint = 0 := by
  apply Order.coheight_eq_zero.mpr
  intro y hy
  have hz : IsGenericPoint c.property.1.genericPoint c.val :=
    c.property.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ c.property)
  have hsub : c.val ⊆ closure ({y} : Set Z) := by
    rw [← hz.def]
    exact specializes_iff_closure_subset.mp hy
  have hrev := c.property.2 isIrreducible_singleton.closure hsub
  exact hz.specializes (hrev (subset_closure (Set.mem_singleton y)))

/-- The actual component inclusion sends its generic point to the original
component generic point of the original Cartier scheme. -/
theorem componentι_genericPoint (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) :
    componentι i c (genericPoint (componentScheme i c)) = i c.property.1.genericPoint := by
  have hc := i.isClosedMap c.val (isClosed_of_mem_irreducibleComponents _ c.property)
  have hl : IsGenericPoint (componentι i c (genericPoint (componentScheme i c))) (i '' c.val) := by
    simpa only [Set.image_univ, range_componentι, hc.closure_eq] using
      (genericPoint_spec (componentScheme i c)).image (componentι i c).continuous
  have hr : IsGenericPoint (i c.property.1.genericPoint) (i '' c.val) := by
    simpa only [hc.closure_eq] using
      (c.property.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ c.property)).image i.continuous
  exact hl.eq hr

/-- The actual inclusion of the original closed fibre is a closed immersion. -/
theorem closedFibre_inclusion_isClosed [IsLocalRing A]
    (q : X ⟶ Spec (.of A)) : IsClosedImmersion (q.fiberι (IsLocalRing.closedPoint A)) := by
  let : IsClosedImmersion ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (IsLocalRing.isClosed_singleton_closedPoint A)
  change IsClosedImmersion (pullback.fst q
    ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A)))
  infer_instance

/-- The original component image lies in the original closed fibre. -/
theorem component_range_subset_closedFibre [IsLocalRing A] (q : X ⟶ Spec (.of A))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A)
    (c : irreducibleComponents Z) :
    Set.range (componentι i c) ⊆ Set.range (q.fiberι (IsLocalRing.closedPoint A)) := by
  rw [range_componentι, q.range_fiberι]
  rintro _ ⟨z, hz, rfl⟩
  exact hv z

/-- The original component map is also a map into the ORIGINAL closed fibre. -/
def componentToFibre [IsLocalRing A] (q : X ⟶ Spec (.of A))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A)
    (c : irreducibleComponents Z) :
    componentScheme i c ⟶ q.fiber (IsLocalRing.closedPoint A) := by
  let := closedFibre_inclusion_isClosed q
  exact liftReducedToClosed (q.fiberι (IsLocalRing.closedPoint A)) (componentι i c)
    (component_range_subset_closedFibre q i hv c)

@[reassoc (attr := simp)]
theorem componentToFibre_fac [IsLocalRing A] (q : X ⟶ Spec (.of A))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A)
    (c : irreducibleComponents Z) :
    componentToFibre q i hv c ≫ q.fiberι (IsLocalRing.closedPoint A) = componentι i c := by
  let := closedFibre_inclusion_isClosed q
  exact liftReducedToClosed_fac (q.fiberι (IsLocalRing.closedPoint A)) (componentι i c)
    (component_range_subset_closedFibre q i hv c)

/-- The original component over the actual residue field of the original
closed base point. There is no ambient coefficient-field choice. -/
abbrev componentOver [IsLocalRing A] (q : X ⟶ Spec (.of A))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A)
    (c : irreducibleComponents Z) :
    OverField.FScheme ((Spec (.of A)).residueField (IsLocalRing.closedPoint A)) :=
  Over.mk (componentToFibre q i hv c ≫ q.fiberToSpecResidueField (IsLocalRing.closedPoint A))

instance componentOver_isProper [IsLocalRing A] (q : X ⟶ Spec (.of A)) [IsProper q]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A)
    (c : irreducibleComponents Z) : IsProper (componentOver q i hv c).hom := by
  let := closedFibre_inclusion_isClosed q
  let : IsClosedImmersion (componentToFibre q i hv c ≫ q.fiberι (IsLocalRing.closedPoint A)) := by
    rw [componentToFibre_fac]
    infer_instance
  let : IsClosedImmersion (componentToFibre q i hv c) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (q.fiberι (IsLocalRing.closedPoint A))
  let : IsProper (q.fiberToSpecResidueField (IsLocalRing.closedPoint A)) := by
    change IsProper (pullback.snd q
      ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A)))
    infer_instance
  change IsProper (componentToFibre q i hv c ≫ _)
  infer_instance

private theorem genericPoint_mem_componentOpen (c : irreducibleComponents Z)
    [IsNoetherian Z] : c.property.1.genericPoint ∈ Z.irreducibleComponentOpen c.val := by
  change c.property.1.genericPoint ∉ ⋃₀ (irreducibleComponents Z \ {c.val})
  rintro ⟨d, ⟨hd, hdc⟩, hzd⟩
  have hgen : IsGenericPoint c.property.1.genericPoint c.val :=
    c.property.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ c.property)
  have hcd : c.val ⊆ d := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hzd)
      (isClosed_of_mem_irreducibleComponents d hd)
  have he : d = c.val := (c.property.2 hd.1 hcd).antisymm hcd
  exact hdc he

/-- The actual open of the reduced component which avoids all other
components of the original Cartier scheme. -/
def componentIsolatingOpen (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian Z]
    (c : irreducibleComponents Z) : (componentScheme i c).Opens :=
  componentToDivisor i c ⁻¹ᵁ Z.irreducibleComponentOpen c.val

theorem componentIsolatingOpen_nonempty (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian Z]
    (c : irreducibleComponents Z) :
    (componentIsolatingOpen i c : Set (componentScheme i c)).Nonempty := by
  have hw : componentToDivisor i c (genericPoint (componentScheme i c)) =
      c.property.1.genericPoint := by
    apply i.isClosedEmbedding.injective
    rw [← Hom.comp_apply, componentToDivisor_fac, componentι_genericPoint]
  refine ⟨genericPoint (componentScheme i c), ?_⟩
  change componentToDivisor i c (genericPoint (componentScheme i c)) ∈
    Z.irreducibleComponentOpen c.val
  rw [hw]
  exact genericPoint_mem_componentOpen c

private theorem componentIsolatingOpen_avoids (i : Z ⟶ X) [IsClosedImmersion i]
    [IsNoetherian Z] (c : irreducibleComponents Z) {x : componentScheme i c}
    (hx : x ∈ componentIsolatingOpen i c) (d : irreducibleComponents Z) (hd : d ≠ c) :
    componentι i c x ∉ i '' d.val := by
  rintro ⟨z, hz, hzx⟩
  have hw : componentToDivisor i c x = z := by
    apply i.isClosedEmbedding.injective
    rw [← Hom.comp_apply, componentToDivisor_fac]
    exact hzx.symm
  change componentToDivisor i c x ∉ ⋃₀ (irreducibleComponents Z \ {c.val}) at hx
  apply hx
  refine ⟨d.val, ⟨d.property, ?_⟩, ?_⟩
  · exact fun he => hd (Subtype.ext he)
  · rwa [hw]

private theorem component_generic_not_closed
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q))) (hdim : ringKrullDim A = 2)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A)
    (c : irreducibleComponents Z) :
    ¬IsClosed ({genericPoint (componentScheme i c)} : Set (componentScheme i c)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have hd : Order.coheight (componentι i c (genericPoint (componentScheme i c))) = 1 := by
    rw [componentι_genericPoint]
    exact coheight_eq_one_of_minimal_cartier_point i hI _ (component_generic_coheight_zero c)
  have hv' : q (componentι i c (genericPoint (componentScheme i c))) =
      IsLocalRing.closedPoint A := by rw [componentι_genericPoint]; exact hv _
  have hn := not_isClosed_of_coheight_one_over_closedPoint q hff hdim _ hd hv'
  intro hc
  apply hn
  simpa only [Set.image_singleton] using (componentι i c).isClosedMap _ hc

/-- The actual function and isolated closed points required for the
vertical-Cartier argument. All components are the original Cartier
support components, with their native reduced structure and original
maps. Nonfield stalks and component-isolating points are produced. -/
theorem exists_base_function_for_verticalCartier
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q))) (hdim : ringKrullDim A = 2)
    (i : Z ⟶ X) [IsClosedImmersion i] [Nonempty Z]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A) :
    ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧
      ∀ c : irreducibleComponents Z, ∃ x : componentScheme i c,
        IsClosed ({x} : Set (componentScheme i c)) ∧
        (∀ d : irreducibleComponents Z, d ≠ c → componentι i c x ∉ i '' d.val) ∧
        ∃ g r : X.presheaf.stalk (componentι i c x),
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (componentι i c x)) ∧
          (componentι i c).stalkMap x g ≠ 0 ∧
          baseStalkMap q (componentι i c x) f = g * r := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  let : IsNoetherian Z := ⟨⟩
  let : Finite (irreducibleComponents Z) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let z : Z := Classical.choice inferInstance
  let : Nonempty (irreducibleComponents Z) :=
    ⟨⟨_root_.irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩⟩
  have hpoints (c : irreducibleComponents Z) :
      ∃ x ∈ componentIsolatingOpen i c, IsClosed ({x} : Set (componentScheme i c)) ∧
        ¬IsField ((componentScheme i c).presheaf.stalk x) := by
    let : IsIntegral (componentOver q i hv c).left := componentScheme_isIntegral i c
    exact exists_closed_nonfield_point_in_open (componentOver q i hv c) (componentIsolatingOpen i c)
      (componentIsolatingOpen_nonempty i c) (component_generic_not_closed q hff hdim i hI hv c)
  choose x hxU hxc hxF using hpoints
  obtain ⟨f, hf, hfm, hfac⟩ := exists_base_function_factor_at_points q hff
    (componentScheme i) (componentι i) x hxF
  refine ⟨f, hf, hfm, fun c => ⟨x c, hxc c, ?_, hfac c⟩⟩
  exact fun d hd => componentIsolatingOpen_avoids i c (hxU c) d hd


private theorem affine_mem_principal_of_height_one_germs
    [IsIntegral X] [IsLocallyNoetherian X] (hN : NormalStalks X)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (a r : Γ(X, U)) (hr : r ≠ 0)
    (h : ∀ (x : X) (hx : x ∈ U), Order.coheight x = 1 →
      X.presheaf.germ U x hx a ∈ Ideal.span {X.presheaf.germ U x hx r}) :
    a ∈ Ideal.span {r} := by
  let R := Γ(X, U)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hN x).2
  let : IsIntegrallyClosed R := isIntegrallyClosed_sections_of_isAffineOpen X U hU
  apply Ideal.mem_span_singleton_of_mem_map_atPrime_height_one hr
  intro P hP hp
  let p : Spec R := ⟨P, hP⟩
  let x := hU.fromSpec p
  have hx : x ∈ U := hU.range_fromSpec.subset ⟨p, rfl⟩
  have hpco : Order.coheight p = 1 := (idealHeight_eq_coheight R p).symm.trans hp
  have hco : Order.coheight x = 1 :=
    (coheight_eq_of_isOpenImmersion hU.fromSpec).trans hpco
  let S := X.presheaf.stalk x
  let : Algebra R S := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime S P := hU.isLocalization_stalk' p hx
  let e : Localization.AtPrime P ≃ₐ[R] S := IsLocalization.algEquiv P.primeCompl _ _
  have hs : algebraMap R S a ∈ Ideal.span {algebraMap R S r} := h x hx hco
  have ht := Ideal.mem_map_of_mem e.symm.toRingHom hs
  rw [Ideal.map_span, Set.image_singleton] at ht
  change e.symm (algebraMap R S a) ∈ Ideal.span {e.symm (algebraMap R S r)} at ht
  rw [e.symm.commutes, e.symm.commutes] at ht
  simpa only [Ideal.map_span, Set.image_singleton] using ht

/-- The original global pullback of a base-ring element. -/
def baseSectionMap (q : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom

/-- Taking the actual global germ of a pulled base function recovers the
original base-to-stalk map used in the numerator factorizations. -/
theorem baseSectionMap_germ (q : X ⟶ Spec (.of A)) (x : X) (a : A) :
    X.presheaf.germ ⊤ x trivial (baseSectionMap q a) = baseStalkMap q x a := by
  change X.presheaf.germ ⊤ x trivial (q.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) =
    q.stalkMap x ((Spec (.of A)).presheaf.germ ⊤ (q x) trivial
      ((Scheme.ΓSpecIso (.of A)).inv a))
  exact (q.germ_stalkMap_apply ⊤ x trivial ((Scheme.ΓSpecIso (.of A)).inv a)).symm

/-- Actual membership at every height-one stalk makes an original global
section belong to the original Cartier ideal power. This uses normality
and all height-one primes, including points outside the vertical support. -/
theorem section_mem_idealPower_of_height_one_germs
    {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalStalks X) (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (n : ℕ) (s : Γ(X, ⊤))
    (hs : ∀ x : X, Order.coheight x = 1 →
      X.presheaf.germ ⊤ x trivial s ∈ (i.ker ^ n).stalkIdeal x) :
    s ∈ RingHom.ker (((i.ker ^ n).subschemeι).app ⊤).hom := by
  let k := (i.ker ^ n).subschemeι
  let N := (Modules.pushforward k).obj (SheafOfModules.unit (i.ker ^ n).subscheme.ringCatSheaf)
  let φ := structureModuleMap k
  change φ.val.app (op ⊤) s = 0
  have hc : Presheaf.equalizerSieve (F := N.val.presheaf) (φ.val.app (op ⊤) s) 0 ∈
      (Opens.grothendieckTopology X) ⊤ := by
    intro x _
    obtain ⟨U, hU, hxU, a, ha, hker⟩ :=
      exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI x
    let : Nonempty U := ⟨⟨x, hxU⟩⟩
    let sU : Γ(X, U) := X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s
    have ha0 : a ≠ 0 := by
      intro hz
      exact zero_ne_one (ha (by simp [hz] : a • (0 : Γ(X, U)) = a • (1 : Γ(X, U))))
    have hp : (i.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {a ^ n} := by
      change (i.ker.ideal ⟨U, hU⟩) ^ n = _
      rw [i.ker_apply ⟨U, hU⟩, hker, Ideal.span_singleton_pow]
    have hsU : sU ∈ (i.ker ^ n).ideal ⟨U, hU⟩ := by
      rw [hp]
      apply affine_mem_principal_of_height_one_germs hN U hU sU (a ^ n) (pow_ne_zero n ha0)
      intro y hy hcy
      have hyI := hs y hcy
      rw [(i.ker ^ n).stalkIdeal_eq_map ⟨U, hU⟩ y hy, hp,
        Ideal.map_span, Set.image_singleton] at hyI
      have he : X.presheaf.germ U y hy sU = X.presheaf.germ ⊤ y trivial s := by
        change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
          X.presheaf.germ U y hy) s = _
        rw [TopCat.Presheaf.germ_res]
      rw [he]
      exact hyI
    refine ⟨U, homOfLE le_top, ?_, hxU⟩
    change N.val.map (homOfLE (show U ≤ ⊤ from le_top)).op (φ.val.app (op ⊤) s) =
      N.val.map (homOfLE (show U ≤ ⊤ from le_top)).op 0
    rw [map_zero, ← PresheafOfModules.naturality_apply]
    change k.app U sU = 0
    apply RingHom.mem_ker.mp
    rwa [(i.ker ^ n).ker_subschemeι_app ⟨U, hU⟩]
  apply N.isSheaf.isSeparated ⊤ _ hc
  intro V q hq
  exact hq


private theorem exists_common_powers_dvd_of_dvr
    {ι : Type u} [Finite ι] [Nonempty ι]
    (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] (a f : ∀ i, R i)
    (ha0 : ∀ i, a i ≠ 0) (hf0 : ∀ i, f i ≠ 0)
    (hau : ∀ i, ¬IsUnit (a i)) (hfu : ∀ i, ¬IsUnit (f i)) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ i : ι,
      (∀ j, a j ^ n ∣ f j ^ m) ∧ Associated (a i ^ n) (f i ^ m) := by
  classical
  let := Fintype.ofFinite ι
  let d (i : ι) := (IsDiscreteValuationRing.addVal (R i) (a i)).toNat
  let e (i : ι) := (IsDiscreteValuationRing.addVal (R i) (f i)).toNat
  have had (i : ι) : IsDiscreteValuationRing.addVal (R i) (a i) = (d i : ℕ∞) :=
    (ENat.natCast_toNat (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha0 i))).symm
  have hfe (i : ι) : IsDiscreteValuationRing.addVal (R i) (f i) = (e i : ℕ∞) :=
    (ENat.natCast_toNat (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hf0 i))).symm
  have hd (i : ι) : 0 < d i :=
    ENat.toNat_pos (IsDiscreteValuationRing.addVal_eq_zero_iff.not.mpr (hau i))
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha0 i))
  have he (i : ι) : 0 < e i :=
    ENat.toNat_pos (IsDiscreteValuationRing.addVal_eq_zero_iff.not.mpr (hfu i))
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hf0 i))
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => (d j : ℚ) / (e j : ℚ)) Finset.univ_nonempty
  have hcross (j : ι) : e i * d j ≤ d i * e j := by
    have hrat := (div_le_div_iff₀ (by exact_mod_cast he j) (by exact_mod_cast he i)).mp
      (hi j (Finset.mem_univ j))
    exact_mod_cast (by simpa only [mul_comm] using hrat :
      (e i : ℚ) * d j ≤ d i * e j)
  refine ⟨d i, e i, hd i, he i, i, ?_, ?_⟩
  · intro j
    apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow, had, hfe]
    simpa only [nsmul_eq_mul, ← Nat.cast_mul] using
      (show ((e i * d j : ℕ) : ℕ∞) ≤ (d i * e j : ℕ) by exact_mod_cast hcross j)
  · apply (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mp
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow, had, hfe]
    simp only [nsmul_eq_mul, mul_comm]

private theorem exists_nonzero_stalkIdeal_generator
    {Z : Scheme.{u}} [IsIntegral X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i)) (x : X) :
    ∃ a : X.presheaf.stalk x, a ≠ 0 ∧ i.ker.stalkIdeal x = Ideal.span {a} := by
  obtain ⟨U, hU, hx, a, ha, hker⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI x
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  have ha0 : a ≠ 0 := by
    intro h
    exact zero_ne_one (ha (by simp [h] : a • (0 : Γ(X, U)) = a • (1 : Γ(X, U))))
  refine ⟨X.presheaf.germ U x hx a, ?_, ?_⟩
  · intro h
    exact ha0 (germ_injective_of_isIntegral X x hx
      (h.trans (map_zero (X.presheaf.germ U x hx).hom).symm))
  · rw [i.ker.stalkIdeal_eq_map ⟨U, hU⟩ x hx, i.ker_apply ⟨U, hU⟩, hker,
      Ideal.map_span, Set.image_singleton]

private theorem stalkIdeal_ker_eq_stalkMap_ker
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    i.ker.stalkIdeal (i z) = RingHom.ker (i.stalkMap z).hom := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show i z ∈ (⊤ : X.Opens) from trivial)
  rw [i.ker.stalkIdeal_eq_map ⟨U, hU⟩ (i z) hxU, i.ker_apply ⟨U, hU⟩,
    ker_stalkMap_eq_map_ker_app i U hU z hxU]

private theorem genericPoint_not_mem_range_cartier
    {Z : Scheme.{u}} [IsIntegral X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i)) :
    genericPoint X ∉ Set.range i := by
  rintro ⟨z, hz⟩
  have hf : IsField (X.presheaf.stalk (i z)) := hz.symm ▸ Field.toIsField X.functionField
  let : Field (X.presheaf.stalk (i z)) := hf.toField
  have hinj : Function.Injective (i.stalkMap z).hom := RingHom.injective _
  have hk : RingHom.ker (i.stalkMap z).hom = ⊥ := by
    ext r
    rw [RingHom.mem_ker, Ideal.mem_bot]
    constructor
    · intro h
      exact hinj (h.trans (map_zero (i.stalkMap z).hom).symm)
    · intro h
      rw [h, map_zero]
  obtain ⟨a, ha0, hgen⟩ := exists_nonzero_stalkIdeal_generator i hI (i z)
  have ha : a ∈ i.ker.stalkIdeal (i z) := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton a)
  rw [stalkIdeal_ker_eq_stalkMap_ker, hk, Ideal.mem_bot] at ha
  exact ha0 ha

/-- Every height-one point of the original Cartier support is the actual
image of a generic point of an original reduced component. -/
theorem height_one_mem_range_is_component_generic
    {Z : Scheme.{u}} [IsIntegral X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (x : X) (hx : Order.coheight x = 1) (hxi : x ∈ Set.range i) :
    ∃ c : irreducibleComponents Z,
      componentι i c (genericPoint (componentScheme i c)) = x := by
  obtain ⟨z, rfl⟩ := hxi
  have hz0 : Order.coheight z = 0 := by
    apply Order.coheight_eq_zero.mpr
    intro w hw
    by_cases hwz : w = z
    · simpa only [hwz] using (le_rfl : z ≤ z)
    · have hiw : i w ≠ i z := i.isClosedEmbedding.injective.ne hwz
      have hg := generic_of_strict_generalization_of_coheight_one hx (hw.map i.continuous) hiw
      exact False.elim (genericPoint_not_mem_range_cartier i hI ⟨w, hg⟩)
  let c : irreducibleComponents Z :=
    ⟨_root_.irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  have hc : IsGenericPoint c.property.1.genericPoint c.val :=
    c.property.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ c.property)
  have hcz : c.property.1.genericPoint ⤳ z := hc.specializes mem_irreducibleComponent
  have he : c.property.1.genericPoint = z :=
    (Specializes.antisymm hcz (Order.coheight_eq_zero.mp hz0 hcz)).eq
  exact ⟨c, by rw [componentι_genericPoint, he]⟩

private theorem normal_coheight_one_stalk_dvr
    [IsIntegral X] [IsLocallyNoetherian X] (hN : NormalStalks X)
    (x : X) (hx : Order.coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  let : IsIntegrallyClosed R := (hN x).2
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  have hp : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R := by
    intro P hP hprime
    exact IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hP)
  let : ValuationRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 2 rfl rfl).mp
      ⟨inferInstance, hp⟩
  have hn : ¬IsField R := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    have hone : ringKrullDim R = 1 := by
      rw [ringKrullDim_stalk_eq_coheight]
      exact_mod_cast hx
    rw [hone] at hzero
    norm_num at hzero
  exact ((IsDiscreteValuationRing.TFAE R hn).out 2 1 rfl rfl).mp
    (inferInstance : ValuationRing R)


/-- The base-to-stalk map has its original scheme-theoretic triangle. -/
theorem baseStalkMap_spec (q : X ⟶ Spec (.of A)) (x : X) :
    Spec.map (CommRingCat.ofHom (baseStalkMap q x)) = X.fromSpecStalk x ≫ q := by
  change Spec.map (StructureSheaf.toStalk A (q x) ≫ q.stalkMap x) = _
  rw [Spec.map_comp]
  have he := congrArg (fun t : Spec ((Spec (.of A)).presheaf.stalk (q x)) ⟶ Spec (.of A) =>
    Spec.map (q.stalkMap x) ≫ t) (Spec.fromSpecStalk_eq' (.of A) (q x))
  exact he.symm.trans (Scheme.SpecMap_stalkMap_fromSpecStalk q (x := x))

/-- Over the original closed base point, the original scalar map carries
the base maximal ideal into the actual point-stalk maximal ideal. -/
theorem baseStalkMap_mem_maximalIdeal [IsLocalRing A]
    (q : X ⟶ Spec (.of A)) (x : X) (hx : q x = IsLocalRing.closedPoint A)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    baseStalkMap q x a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hp := congrArg (fun f : Spec (X.presheaf.stalk x) ⟶ Spec (.of A) =>
    f (IsLocalRing.closedPoint (X.presheaf.stalk x))) (baseStalkMap_spec q x)
  simp only [Hom.comp_apply, Scheme.fromSpecStalk_closedPoint, hx] at hp
  have hk : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (baseStalkMap q x) =
      IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal hp
  change a ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (baseStalkMap q x)
  rwa [hk]

private def idealImageIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    idealModule i ≅ idealModule i.ker.subschemeι := by
  let τ := idealPullbackMap i.ker.subschemeι i (𝟙 X) i.toImage
    (by simpa only [Category.comp_id] using i.toImage_imageι)
  let : IsIso τ := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (((Modules.pullbackId X).app (idealModule i.ker.subschemeι)).symm ≪≫ asIso τ).symm

private def idealSuccPowerIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i)) (n : ℕ) :
    Modules.tensorSheaf X (idealModule i) (idealModule (i.ker ^ (n + 1)).subschemeι) ≅
      idealModule (i.ker ^ (n + 2)).subschemeι :=
  idealProductIso i (i.ker ^ (n + 1)).subschemeι hI ≪≫
    eqToIso (congrArg (fun J : X.IdealSheafData => idealModule J.subschemeι) (by
      rw [IdealSheafData.ker_subschemeι, pow_succ' i.ker (n + 1)]))

private def idealFirstPowerIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    idealModule i ≅ idealModule (i.ker ^ (0 + 1)).subschemeι :=
  idealImageIso i ≪≫
    eqToIso (congrArg (fun J : X.IdealSheafData => idealModule J.subschemeι)
      (show i.ker = i.ker ^ (0 + 1) by rw [Nat.zero_add, pow_one]))

private theorem ideal_positive_power_isLocallyRankOne
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i)) (n : ℕ) :
    Modules.Invertible.IsLocallyRankOne X (idealModule (i.ker ^ (n + 1)).subschemeι) := by
  induction n with
  | zero =>
      exact Modules.Invertible.isLocallyRankOne_of_iso X (idealFirstPowerIso i) hI
  | succ n ih =>
      exact Modules.Invertible.isLocallyRankOne_of_iso X (idealSuccPowerIso i hI n)
        (Modules.Invertible.tensorLineBundle X ⟨idealModule i, hI⟩
          ⟨idealModule (i.ker ^ (n + 1)).subschemeι, ih⟩).property

/-- Positive powers of the ORIGINAL ideal restrict trivially wherever its
original restriction does. The recursion uses the native canonical ideal
multiplication, tensor pullback, and structure-module unit isomorphisms. -/
private theorem positivePower_trivial_of_pullback_ideal_trivial
    {Z C : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i)) (j : C ⟶ X)
    (htriv : Nonempty ((Modules.pullback j).obj (idealModule i) ≅
      SheafOfModules.unit C.ringCatSheaf)) (n : ℕ) :
    Nonempty ((Modules.pullback j).obj (idealModule (i.ker ^ (n + 1)).subschemeι) ≅
      SheafOfModules.unit C.ringCatSheaf) := by
  obtain ⟨e⟩ := htriv
  induction n with
  | zero =>
      exact ⟨(Modules.pullback j).mapIso (idealFirstPowerIso i).symm ≪≫ e⟩
  | succ n ih =>
      obtain ⟨en⟩ := ih
      let : IsIso (Modules.pullbackTensorMap j (idealModule i)
          (idealModule (i.ker ^ (n + 1)).subschemeι)) :=
        Modules.Pullback.Tensor.pullbackTensorMap_isIso j _ _
      exact ⟨(Modules.pullback j).mapIso (idealSuccPowerIso i hI n).symm ≪≫
        asIso (Modules.pullbackTensorMap j (idealModule i)
          (idealModule (i.ker ^ (n + 1)).subschemeι)) ≪≫
        Modules.tensorSheafIso C e en ≪≫
        Modules.tensorSheafLeftUnit C (SheafOfModules.unit C.ringCatSheaf)⟩

private def componentIdealTrivial_of_conormalTrivial
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z)
    (e : (Modules.pullback i).obj (idealModule i) ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback (componentι i c)).obj (idealModule i) ≅
      SheafOfModules.unit (componentScheme i c).ringCatSheaf :=
  (Modules.pullbackCongr (componentToDivisor_fac i c).symm).app (idealModule i) ≪≫
    ((Modules.pullbackComp (componentToDivisor i c) i).app (idealModule i)).symm ≪≫
    (Modules.pullback (componentToDivisor i c)).mapIso e ≪≫
    Modules.pullbackUnitIso (componentToDivisor i c)

private theorem nontrivial_of_nonzero_section_not_isIso
    {k : Type u} [Field k] (C : OverField.FScheme k)
    [IsProper C.hom] [IsIntegral C.left] (M : C.left.Modules)
    (s : SheafOfModules.unit C.left.ringCatSheaf ⟶ M) (hs : s ≠ 0) (hns : ¬IsIso s) :
    ¬Nonempty (M ≅ SheafOfModules.unit C.left.ringCatSheaf) := by
  rintro ⟨e⟩
  have hse : s ≫ e.hom ≠ 0 := by
    intro h
    exact hs ((cancel_mono e.hom).mp (h.trans (zero_comp).symm))
  let : IsIso (s ≫ e.hom) := unit_endomorphism_isIso_of_ne_zero C (s ≫ e.hom) hse
  exact hns ((isIso_comp_right_iff s e.hom).mp inferInstance)

/-- The original vertical Cartier data produce a positive ideal-power
section which generates at an ORIGINAL component generic point, together
with the original isolated closed-point factorization of its base function.
No generic membership or section is a premise. -/
theorem exists_power_section_generating_component
    {Z : Scheme.{u}}
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q))) (hdim : ringKrullDim A = 2)
    (hN : NormalStalks X) (i : Z ⟶ X) [IsClosedImmersion i] [Nonempty Z]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A) :
    ∃ (f : A) (m n : ℕ) (c : irreducibleComponents Z),
      f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧ 0 < m ∧ 0 < n ∧
      baseSectionMap q (f ^ m) ∈ RingHom.ker (((i.ker ^ n).subschemeι).app ⊤).hom ∧
      (i.ker ^ n).stalkIdeal (componentι i c (genericPoint (componentScheme i c))) =
        Ideal.span {X.presheaf.germ ⊤ (componentι i c (genericPoint (componentScheme i c)))
          trivial (baseSectionMap q (f ^ m))} ∧
      ∃ x : componentScheme i c,
        IsClosed ({x} : Set (componentScheme i c)) ∧
        (∀ d : irreducibleComponents Z, d ≠ c → componentι i c x ∉ i '' d.val) ∧
        ∃ g r : X.presheaf.stalk (componentι i c x),
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (componentι i c x)) ∧
          (componentι i c).stalkMap x g ≠ 0 ∧
          baseStalkMap q (componentι i c x) f = g * r := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ q)
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ q)
  let : IsNoetherian Z := ⟨⟩
  let : Finite (irreducibleComponents Z) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let z : Z := Classical.choice inferInstance
  let : Nonempty (irreducibleComponents Z) :=
    ⟨⟨_root_.irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩⟩
  obtain ⟨f, hf, hfm, hpoints⟩ := exists_base_function_for_verticalCartier q hff hdim i hI hv
  let η (c : irreducibleComponents Z) := componentι i c (genericPoint (componentScheme i c))
  have hη (c : irreducibleComponents Z) : Order.coheight (η c) = 1 := by
    dsimp only [η]
    rw [componentι_genericPoint]
    exact coheight_eq_one_of_minimal_cartier_point i hI _ (component_generic_coheight_zero c)
  let R (c : irreducibleComponents Z) := X.presheaf.stalk (η c)
  let (c : irreducibleComponents Z) : IsDiscreteValuationRing (R c) :=
    normal_coheight_one_stalk_dvr hN (η c) (hη c)
  choose a ha0 haI using fun c => exists_nonzero_stalkIdeal_generator i hI (η c)
  have hau (c : irreducibleComponents Z) : ¬IsUnit (a c) := by
    have hsupport : η c ∈ i.ker.support := by
      dsimp only [η]
      rw [componentι_genericPoint]
      exact i.range_subset_ker_support ⟨_, rfl⟩
    have hnt := (i.ker.stalkIdeal_ne_top_iff_mem_support (η c)).mpr hsupport
    intro hu
    apply hnt
    apply (i.ker.stalkIdeal (η c)).eq_top_of_isUnit_mem _ hu
    rw [haI c]
    exact Ideal.subset_span (Set.mem_singleton (a c))
  let F (c : irreducibleComponents Z) : R c := baseStalkMap q (η c) f
  have hF0 (c : irreducibleComponents Z) : F c ≠ 0 := by
    intro h
    exact hf (baseStalkMap_injective q (η c)
      (h.trans (map_zero (baseStalkMap q (η c))).symm))
  have hFu (c : irreducibleComponents Z) : ¬IsUnit (F c) := by
    have hp : q (η c) = IsLocalRing.closedPoint A := by
      dsimp only [η]
      rw [componentι_genericPoint]
      exact hv _
    exact baseStalkMap_mem_maximalIdeal q (η c) hp f hfm
  obtain ⟨m, n, hm, hn, c, hdiv, hgen⟩ :=
    exists_common_powers_dvd_of_dvr (fun c => R c) a F ha0 hF0 hau hFu
  have hmem : baseSectionMap q (f ^ m) ∈
      RingHom.ker (((i.ker ^ n).subschemeι).app ⊤).hom := by
    apply section_mem_idealPower_of_height_one_germs hN i hI n
    intro y hy
    by_cases hyi : y ∈ Set.range i
    · obtain ⟨d, rfl⟩ := height_one_mem_range_is_component_generic i hI y hy hyi
      change X.presheaf.germ ⊤ (η d) trivial (baseSectionMap q (f ^ m)) ∈
        (i.ker ^ n).stalkIdeal (η d)
      rw [IdealSheafData.stalkIdeal_pow, haI d, Ideal.span_singleton_pow,
        baseSectionMap_germ, map_pow, Ideal.mem_span_singleton]
      exact hdiv d
    · have hnot : y ∉ i.ker.support := by
        have he : (i.ker.support : Set X) = Set.range i :=
          (Scheme.Hom.support_ker i).trans i.isClosedEmbedding.isClosed_range.closure_eq
        change y ∉ (i.ker.support : Set X)
        rwa [he]
      rw [IdealSheafData.stalkIdeal_pow,
        i.ker.stalkIdeal_eq_top_of_notMem_support y hnot]
      rw [Ideal.top_pow]
      exact Submodule.mem_top
  have hgen' : (i.ker ^ n).stalkIdeal (η c) =
      Ideal.span {X.presheaf.germ ⊤ (η c) trivial (baseSectionMap q (f ^ m))} := by
    rw [IdealSheafData.stalkIdeal_pow, haI c, Ideal.span_singleton_pow,
      baseSectionMap_germ, map_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hgen
  exact ⟨f, m, n, c, hf, hfm, hm, hn, hmem, hgen', hpoints c⟩

private theorem principal_cancel_of_prime_radical
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {a g b : R} (ha : a ≠ 0) (hprime : (Ideal.span {a}).radical.IsPrime)
    (hg : g ∉ (Ideal.span {a}).radical) (hgb : g * b ∈ Ideal.span {a}) :
    b ∈ Ideal.span {a} := by
  let Q := (Ideal.span {a}).radical
  let : Q.IsPrime := hprime
  have haQ : a ∈ Q := Ideal.le_radical (Ideal.subset_span (Set.mem_singleton a))
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact ha (by simpa only [h, Ideal.mem_bot] using haQ)
  apply Ideal.mem_span_singleton_of_mem_map_atPrime_height_one ha
  intro P hP hp
  let α := algebraMap R (Localization.AtPrime P)
  by_cases haP : a ∈ P
  · have hQP : Q ≤ P :=
      (hP.radical_le_iff).mpr (P.span_singleton_le_iff_mem.mpr haP)
    have he : Q = P := by
      by_contra hne
      have hlt : Q < P := lt_of_le_of_ne hQP hne
      have hd : Q.height < 1 := by
        simpa only [hp] using Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      exact hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hd))
    have hgP : g ∉ P := he ▸ hg
    have hu : IsUnit (α g) :=
      IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P) ⟨g, hgP⟩
    obtain ⟨v, hv⟩ := hu
    have hm : α g * α b ∈ (Ideal.span {a}).map α := by
      simpa only [map_mul] using Ideal.mem_map_of_mem α hgb
    have hh := ((Ideal.span {a}).map α).mul_mem_left (↑v⁻¹ : Localization.AtPrime P) hm
    rw [← hv] at hh
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hh
  · have hu : IsUnit (α a) :=
      IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P) ⟨a, haP⟩
    have ht : (Ideal.span {a}).map α = ⊤ :=
      ((Ideal.span {a}).map α).eq_top_of_isUnit_mem
        (Ideal.mem_map_of_mem α (Ideal.subset_span (Set.mem_singleton a))) hu
    rw [ht]
    exact Submodule.mem_top

private theorem stalkIdeal_radical (I : X.IdealSheafData) (x : X) :
    I.radical.stalkIdeal x = (I.stalkIdeal x).radical := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let P := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk ⟨x, hx⟩
  rw [I.radical.stalkIdeal_eq_map ⟨U, hU⟩ x hx, I.stalkIdeal_eq_map ⟨U, hU⟩ x hx]
  exact IsLocalization.map_radical P.primeCompl (X.presheaf.stalk x) (I.ideal ⟨U, hU⟩)

/-- At an actual point avoiding the other original Cartier-support
components, the radical of the ORIGINAL stalk ideal is the ORIGINAL
reduced component-inclusion stalk kernel. No reducedness of Z is assumed. -/
theorem radical_stalkIdeal_eq_component_kernel_at_isolated
    {Z : Scheme.{u}} [IsNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (c : irreducibleComponents Z) (x : componentScheme i c)
    (hx : ∀ d : irreducibleComponents Z, d ≠ c → componentι i c x ∉ i '' d.val) :
    (i.ker.stalkIdeal (componentι i c x)).radical =
      RingHom.ker ((componentι i c).stalkMap x).hom := by
  classical
  let : Finite (irreducibleComponents Z) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let S : Set (irreducibleComponents Z) := {d | d ≠ c}
  let W : X.Opens := ⟨(⋃ d ∈ S, i '' d.val)ᶜ,
    ((Set.toFinite S).isClosed_biUnion
      (fun d _ => i.isClosedMap d.val
        (isClosed_of_mem_irreducibleComponents _ d.property))).isOpen_compl⟩
  have hxW : componentι i c x ∈ W := by
    intro h
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
    obtain ⟨hdc, hdx⟩ := Set.mem_iUnion.mp hd
    exact hx d hdc hdx
  have hsupport : (i.ker.support : Set X) = Set.range i :=
    (Scheme.Hom.support_ker i).trans i.isClosedEmbedding.isClosed_range.closure_eq
  have hlocal (y : X) (hy : y ∈ W) : y ∈ i.ker.support ↔ y ∈ i '' c.val := by
    have hyker : y ∈ i.ker.support ↔ y ∈ Set.range i := by
      change y ∈ (i.ker.support : Set X) ↔ y ∈ Set.range i
      rw [hsupport]
    rw [hyker]
    constructor
    · rintro ⟨z, rfl⟩
      let d : irreducibleComponents Z :=
        ⟨_root_.irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
      have hzd : z ∈ d.val := mem_irreducibleComponent
      by_cases hdc : d = c
      · exact ⟨z, hdc ▸ hzd, rfl⟩
      · exact False.elim (hy (Set.mem_iUnion.mpr ⟨d,
          Set.mem_iUnion.mpr ⟨hdc, ⟨z, hzd, rfl⟩⟩⟩))
    · exact fun ⟨z, _, hz⟩ => ⟨z, hz⟩
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
  have hpre : hU.fromSpec ⁻¹' (i.ker.support : Set X) = hU.fromSpec ⁻¹' (i '' c.val) := by
    ext p
    exact hlocal (hU.fromSpec p) (hUW (hU.range_fromSpec.subset ⟨p, rfl⟩))
  have hideal : i.ker.radical.ideal ⟨U, hU⟩ = (componentIdeal i c).ideal ⟨U, hU⟩ := by
    rw [← IdealSheafData.vanishingIdeal_support]
    change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (i.ker.support : Set X)) =
      PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (i '' c.val))
    rw [hpre]
  have hstalk : i.ker.radical.stalkIdeal (componentι i c x) =
      (componentIdeal i c).stalkIdeal (componentι i c x) := by
    rw [i.ker.radical.stalkIdeal_eq_map ⟨U, hU⟩ _ hxU,
      (componentIdeal i c).stalkIdeal_eq_map ⟨U, hU⟩ _ hxU, hideal]
  rw [stalkIdeal_radical] at hstalk
  refine hstalk.trans ?_
  have hk : (componentι i c).ker = componentIdeal i c :=
    (componentIdeal i c).ker_subschemeι
  rw [← hk]
  exact stalkIdeal_ker_eq_stalkMap_ker (componentι i c) x

private theorem principal_pow_cancel_of_prime_radical
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {a g b : R} (ha : a ≠ 0) (hprime : (Ideal.span {a}).radical.IsPrime)
    (hg : g ∉ (Ideal.span {a}).radical) (m : ℕ) (hgb : g ^ m * b ∈ Ideal.span {a}) :
    b ∈ Ideal.span {a} := by
  revert b
  induction m with
  | zero =>
      intro b hb
      simpa only [pow_zero, one_mul] using hb
  | succ m ih =>
      intro b hb
      apply ih
      apply principal_cancel_of_prime_radical ha hprime hg
      simpa only [pow_succ', mul_assoc] using hb

/-- Actual component isolation and the original nonzero component image
of g make the original ideal-power section vanish to first order at the
selected point. Prime radical is derived, not a hypothesis. -/
theorem power_section_mem_maximal_mul_at_isolated
    {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNoetherian Z]
    (hN : NormalStalks X) (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (c : irreducibleComponents Z) (x : componentScheme i c)
    (hx : ∀ d : irreducibleComponents Z, d ≠ c → componentι i c x ∉ i '' d.val)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (s : Γ(X, ⊤))
    (g r : X.presheaf.stalk (componentι i c x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (componentι i c x)))
    (hg : (componentι i c).stalkMap x g ≠ 0)
    (hfac : X.presheaf.germ ⊤ (componentι i c x) trivial s = g ^ m * r ^ m)
    (hs : X.presheaf.germ ⊤ (componentι i c x) trivial s ∈
      (i.ker ^ n).stalkIdeal (componentι i c x)) :
    X.presheaf.germ ⊤ (componentι i c x) trivial s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (componentι i c x)) *
        (i.ker ^ n).stalkIdeal (componentι i c x) := by
  let R := X.presheaf.stalk (componentι i c x)
  let : IsIntegrallyClosed R := (hN (componentι i c x)).2
  obtain ⟨a, ha, haI⟩ := exists_nonzero_stalkIdeal_generator i hI (componentι i c x)
  have hp : (i.ker ^ n).stalkIdeal (componentι i c x) = Ideal.span {a ^ n} := by
    rw [IdealSheafData.stalkIdeal_pow, haI, Ideal.span_singleton_pow]
  have hrad : ((i.ker ^ n).stalkIdeal (componentι i c x)).radical =
      RingHom.ker ((componentι i c).stalkMap x).hom := by
    rw [IdealSheafData.stalkIdeal_pow, Ideal.radical_pow _ (Nat.ne_zero_of_lt hn)]
    exact radical_stalkIdeal_eq_component_kernel_at_isolated i c x hx
  have hprime : (Ideal.span {a ^ n}).radical.IsPrime := by
    rw [← hp, hrad]
    exact RingHom.ker_isPrime ((componentι i c).stalkMap x).hom
  have hgn : g ∉ (Ideal.span {a ^ n}).radical := by
    rw [← hp, hrad, RingHom.mem_ker]
    exact hg
  have hgr : g ^ m * r ^ m ∈ Ideal.span {a ^ n} := by
    rw [← hp, ← hfac]
    exact hs
  have hr : r ^ m ∈ (i.ker ^ n).stalkIdeal (componentι i c x) := by
    rw [hp]
    exact principal_pow_cancel_of_prime_radical (pow_ne_zero n ha) hprime hgn m hgr
  have hgp : g ^ m ∈ IsLocalRing.maximalIdeal R := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    rw [pow_succ]
    exact (IsLocalRing.maximalIdeal R).mul_mem_left _ hgm
  rw [hfac]
  exact Ideal.mul_mem_mul hgp hr

/-- The ORIGINAL conormal of a nonempty effective Cartier divisor
supported set-theoretically in the ORIGINAL closed fibre of a normal
proper birational modification of a two-dimensional normal Noetherian
local domain is not trivial. No regularity, excellence, perfectness,
coefficient field, component splitting, or resolution hypothesis is used. -/
theorem conormal_not_trivial_of_vertical_cartier
    {Z : Scheme.{u}}
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q))) (hdim : ringKrullDim A = 2)
    (hN : NormalStalks X) (i : Z ⟶ X) [IsClosedImmersion i] [Nonempty Z]
    (hI : Modules.Invertible.IsLocallyRankOne X (idealModule i))
    (hv : ∀ z : Z, q (i z) = IsLocalRing.closedPoint A) :
    ¬Nonempty ((Modules.pullback i).obj (idealModule i) ≅
      SheafOfModules.unit Z.ringCatSheaf) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ q)
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ q)
  let : IsNoetherian Z := ⟨⟩
  obtain ⟨f, m, n, c, _, _, hm, hn, hs, hgen, x, _, havoid, g, r, hgm, hg, hfac⟩ :=
    exists_power_section_generating_component q hff hdim hN i hI hv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let k := (i.ker ^ (d + 1)).subschemeι
  let s : Γ(X, ⊤) := baseSectionMap q (f ^ m)
  let j := componentι i c
  have hIk : Modules.Invertible.IsLocallyRankOne X (idealModule k) :=
    ideal_positive_power_isLocallyRankOne i hI d
  have hsk : s ∈ RingHom.ker k.appTop.hom := hs
  let σ := idealGlobalSection k s hsk
  let σC := (Modules.pullbackUnitIso j).inv ≫ (Modules.pullback j).map σ
  have hσne : σC ≠ 0 :=
    idealGlobalSection_pullback_ne_zero_of_generator k hIk j s hsk
      (genericPoint (componentScheme i c)) (by
        simpa only [k, j, s, IdealSheafData.ker_subschemeι] using hgen)
  have hmem : X.presheaf.germ ⊤ (j x) trivial s ∈ (i.ker ^ (d + 1)).stalkIdeal (j x) := by
    have ht := idealGlobalSection_germ_mem_stalkIdeal k s hsk (j x)
    simpa only [k, IdealSheafData.ker_subschemeι] using ht
  have hfac' : X.presheaf.germ ⊤ (j x) trivial s = g ^ m * r ^ m := by
    change X.presheaf.germ ⊤ (componentι i c x) trivial (baseSectionMap q (f ^ m)) = _
    rw [baseSectionMap_germ, map_pow, hfac, mul_pow]
  have hmax : X.presheaf.germ ⊤ (j x) trivial s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j x)) * k.ker.stalkIdeal (j x) := by
    have ht := power_section_mem_maximal_mul_at_isolated hN i hI c x havoid
      m (d + 1) hm hn s g r hgm hg hfac' hmem
    simpa only [k, IdealSheafData.ker_subschemeι] using ht
  have hσni : ¬IsIso σC :=
    idealGlobalSection_pullback_not_isIso_of_mem_maximal_mul k hIk j s hsk x hmax
  let C := componentOver q i hv c
  let : IsIntegral C.left := componentScheme_isIntegral i c
  let : IsProper C.hom := componentOver_isProper q i hv c
  have hnontriv := nontrivial_of_nonzero_section_not_isIso C
    ((Modules.pullback j).obj (idealModule k)) σC hσne hσni
  rintro ⟨e⟩
  apply hnontriv
  exact positivePower_trivial_of_pullback_ideal_trivial i hI j
    ⟨componentIdealTrivial_of_conormalTrivial i c e⟩ d

end AlgebraicGeometry.Scheme.VerticalCartier
