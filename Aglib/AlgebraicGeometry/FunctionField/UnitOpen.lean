/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Common affine charts for finitely many function-field units

Source constructs one inhabited affine open representing finitely many actual function-field
units, and an injective actual section-ring lift of a finitely generated subring.

Source: `R5Lab.Aglib.AlgebraicGeometry.FunctionField.UnitOpen`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3224a630d1af8f050e8cd2108a016f645758e97f6fd3f671f884933aa8dfa319`. Selected lines: [[30, 132]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
variable (X : Scheme.{u}) [IsIntegral X]

/-- Every nonempty open of an integral scheme contains its generic point. -/
theorem genericPoint_mem_nonempty_open (U : X.Opens) [hU : Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- Restricting an actual unit section preserves its function-field unit. -/
theorem germToFunctionField_restrict_units {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : U ⟶ V) (s : Γ(X, V)ˣ) :
    Units.map (X.germToFunctionField U).hom.toMonoidHom
      (Units.map (X.presheaf.map i.op).hom.toMonoidHom s) =
        Units.map (X.germToFunctionField V).hom.toMonoidHom s := by
  apply Units.ext
  exact X.presheaf.germ_res_apply i (genericPoint X)
    (genericPoint_mem_nonempty_open X U) s

/-- A finite family of function-field units has actual unit representatives
on one nonempty affine open, with equality under the canonical generic germ. -/
theorem exists_nonempty_affine_unit_open {ι : Type*} [Finite ι]
    (f : ι → X.functionFieldˣ) :
    ∃ U ∈ X.affineOpens, ∃ s : ι → Γ(X, U)ˣ, ∃ _ : Nonempty U,
      ∀ i, Units.map (X.germToFunctionField U).hom.toMonoidHom (s i) = f i := by
  classical
  choose V hV t hn ht hu using fun i => exists_isUnit_germ_eq X (f i) (f i).ne_zero
  let (i : ι) : Nonempty (V i) := hn i
  have hx : genericPoint X ∈ ⨅ i, V i := by
    change genericPoint X ∈ (((⨅ i, V i) : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun i => genericPoint_mem_nonempty_open X (V i)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  let : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  let j (i : ι) : U ⟶ V i := homOfLE (hUV.trans (iInf_le V i))
  let s (i : ι) : Γ(X, U)ˣ :=
    Units.map (X.presheaf.map (j i).op).hom.toMonoidHom (hu i).unit
  refine ⟨U, hU, s, inferInstance, ?_⟩
  intro i
  rw [show s i = Units.map (X.presheaf.map (j i).op).hom.toMonoidHom (hu i).unit from rfl,
    germToFunctionField_restrict_units]
  apply Units.ext
  change X.germToFunctionField (V i) ((hu i).unit : Γ(X, V i)) = (f i : X.functionField)
  rw [(hu i).unit_spec]
  exact ht i

/-- The section ring identifies with its actual image in the function field. -/
def germToFunctionFieldRangeEquiv (U : X.Opens) [Nonempty U] :
    Γ(X, U) ≃+* (X.germToFunctionField U).hom.range :=
  RingEquiv.ofBijective (X.germToFunctionField U).hom.rangeRestrict
    ⟨fun _ _ h => X.germToFunctionField_injective U (congrArg Subtype.val h),
      (X.germToFunctionField U).hom.rangeRestrict_surjective⟩

/-- Lift a subring of regular functions through the injective generic germ map. -/
def sectionRingLift (U : X.Opens) [Nonempty U] (R : Subring X.functionField)
    (hR : R ≤ (X.germToFunctionField U).hom.range) : R →+* Γ(X, U) :=
  (germToFunctionFieldRangeEquiv X U).symm.toRingHom.comp (Subring.inclusion hR)

@[simp] theorem germ_sectionRingLift (U : X.Opens) [Nonempty U]
    (R : Subring X.functionField) (hR : R ≤ (X.germToFunctionField U).hom.range) (r : R) :
    X.germToFunctionField U (sectionRingLift X U R hR r) = (r : X.functionField) := by
  exact congrArg (fun t : (X.germToFunctionField U).hom.range => (t : X.functionField))
    ((germToFunctionFieldRangeEquiv X U).apply_symm_apply (Subring.inclusion hR r))

theorem germ_comp_sectionRingLift (U : X.Opens) [Nonempty U]
    (R : Subring X.functionField) (hR : R ≤ (X.germToFunctionField U).hom.range) :
    (X.germToFunctionField U).hom.comp (sectionRingLift X U R hR) = R.subtype := by
  ext r
  exact germ_sectionRingLift X U R hR r

theorem sectionRingLift_injective (U : X.Opens) [Nonempty U]
    (R : Subring X.functionField) (hR : R ≤ (X.germToFunctionField U).hom.range) :
    Function.Injective (sectionRingLift X U R hR) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (X.germToFunctionField U) hab
  simpa using h

/-- A finite set of rational functions generates a ring of regular sections on
one nonempty affine open; the lift is compatible with the actual generic germ. -/
theorem exists_nonempty_affine_subring_lift (data : Finset X.functionField) :
    ∃ U ∈ X.affineOpens, ∃ _ : Nonempty U,
      ∃ lift : Subring.closure (data : Set X.functionField) →+* Γ(X, U),
        Function.Injective lift ∧ (X.germToFunctionField U).hom.comp lift =
          (Subring.closure (data : Set X.functionField)).subtype := by
  classical
  let f (a : data) : X.functionFieldˣ :=
    if ha : (a : X.functionField) = 0 then 1 else Units.mk0 (a : X.functionField) ha
  obtain ⟨U, hU, s, hn, hs⟩ := exists_nonempty_affine_unit_open X f
  let : Nonempty U := hn
  have hR : Subring.closure (data : Set X.functionField) ≤
      (X.germToFunctionField U).hom.range := by
    apply Subring.closure_le.mpr
    intro a ha
    change a ∈ (X.germToFunctionField U).hom.range
    by_cases hzero : a = 0
    · rw [hzero]
      exact (X.germToFunctionField U).hom.range.zero_mem
    · let a' : data := ⟨a, ha⟩
      refine ⟨(s a' : Γ(X, U)), ?_⟩
      have h := congrArg (fun t : X.functionFieldˣ => (t : X.functionField)) (hs a')
      simpa [f, a', hzero] using h
  exact ⟨U, hU, hn, sectionRingLift X U _ hR, sectionRingLift_injective X U _ hR,
    germ_comp_sectionRingLift X U _ hR⟩

end AlgebraicGeometry.Scheme
