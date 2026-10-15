/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Global-section cycles computing actual Zariski cohomology

This is the resolution-comparison foundation for affine acyclicity. For an
injective resolution of the actual additive sheaf, global-section cycles
surject onto `Sheaf.H`, and a positive-degree cycle is zero precisely when it
is a global-section boundary. The resulting quotient is additively equivalent
to the existing Ext cohomology. No affine vanishing theorem is assumed here.

The homological input is mathlib's `InjectiveResolution.extMk`, its surjectivity,
and its boundary criterion, at mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. This file specializes that verified
comparison to actual global sections using the constant-sheaf adjunction.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.AffineAcyclicity` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X : Scheme.{u}}

/-- Maps from the actual constant integer sheaf are global sections. -/
def integerSheafHomEquiv (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ A) ≃+ A.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).homAddEquiv _ A).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

theorem integerSheafHomEquiv_comp
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ A) (g : A ⟶ B) :
    integerSheafHomEquiv B (f ≫ g) = g.hom.app (op ⊤) (integerSheafHomEquiv A f) := by
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    ((constantSheafAdj _ _ isTerminalTop).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

theorem integerSheafHomEquiv_symm_comp
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (g : A ⟶ B) (s : A.obj.obj (op ⊤)) :
    (integerSheafHomEquiv A).symm s ≫ g =
      (integerSheafHomEquiv B).symm (g.hom.app (op ⊤) s) := by
  apply (integerSheafHomEquiv B).injective
  simp [integerSheafHomEquiv_comp]

variable {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  (R : InjectiveResolution A)

/-- Global sections of the `n`th object of an actual additive-sheaf resolution. -/
abbrev resolutionSections (n : ℕ) := (R.cocomplex.X n).obj.obj (op ⊤)

/-- The differential on global sections of the resolution. -/
abbrev resolutionSectionDifferential (n m : ℕ) :
    resolutionSections R n →+ resolutionSections R m :=
  ((R.cocomplex.d n m).hom.app (op ⊤)).hom

/-- Actual global-section cycles, without introducing another cohomology object. -/
abbrev resolutionSectionCycles (n : ℕ) :=
  (resolutionSectionDifferential R n (n + 1)).ker

/-- A cycle of global sections represents a class in the existing Ext cohomology. -/
def resolutionSectionClass (n : ℕ) : resolutionSectionCycles R n →+ Sheaf.H.{u + 1} A n where
  toFun s := R.extMk ((integerSheafHomEquiv _).symm s.val) (n + 1) rfl (by
    rw [integerSheafHomEquiv_symm_comp]
    exact (integerSheafHomEquiv _).symm.map_eq_zero_iff.mpr s.property)
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero, InjectiveResolution.extMk_zero]
  map_add' s t := by
    simpa only [AddSubgroup.coe_add, map_add] using
      (R.add_extMk ((integerSheafHomEquiv _).symm s.val)
        ((integerSheafHomEquiv _).symm t.val) (n + 1) rfl _ _).symm

/-- Every actual cohomology class has a global-section cycle representative. -/
theorem resolutionSectionClass_surjective (n : ℕ) :
    Function.Surjective (resolutionSectionClass R n) := by
  intro x
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  let s := integerSheafHomEquiv (R.cocomplex.X n) f
  have hs : resolutionSectionDifferential R n (n + 1) s = 0 := by
    rw [← integerSheafHomEquiv_comp, hf, map_zero]
  refine ⟨⟨s, hs⟩, ?_⟩
  simp [resolutionSectionClass, s]

/-- A positive-degree cycle is zero in actual cohomology exactly when it is
the differential of a global section in the preceding degree. -/
theorem resolutionSectionClass_eq_zero_iff (n : ℕ)
    (s : resolutionSectionCycles R (n + 1)) :
    resolutionSectionClass R (n + 1) s = 0 ↔
      ∃ t : resolutionSections R n, resolutionSectionDifferential R n (n + 1) t = s.val := by
  rw [resolutionSectionClass, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    R.extMk_eq_zero_iff _ _ _ _ n rfl]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨integerSheafHomEquiv _ g, ?_⟩
    rw [← integerSheafHomEquiv_comp, hg, AddEquiv.apply_symm_apply]
  · rintro ⟨t, ht⟩
    refine ⟨(integerSheafHomEquiv _).symm t, ?_⟩
    rw [integerSheafHomEquiv_symm_comp]
    exact congrArg (integerSheafHomEquiv _).symm ht

/-- Boundaries as a homomorphism into global-section cycles. -/
def resolutionSectionBoundary (n : ℕ) :
    resolutionSections R n →+ resolutionSectionCycles R (n + 1) where
  toFun s := ⟨resolutionSectionDifferential R n (n + 1) s, by
    exact congrArg (fun f : R.cocomplex.X n ⟶ R.cocomplex.X (n + 1 + 1) ↦
      f.hom.app (op ⊤) s) (R.cocomplex.d_comp_d n (n + 1) (n + 1 + 1))⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ _ _)

theorem resolutionSectionClass_ker (n : ℕ) :
    (resolutionSectionClass R (n + 1)).ker = (resolutionSectionBoundary R n).range := by
  ext s
  rw [AddMonoidHom.mem_ker, resolutionSectionClass_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, congrArg Subtype.val ht⟩

/-- Actual positive-degree Zariski cohomology is the quotient of global-section
cycles by global-section boundaries in any injective resolution. -/
def resolutionSectionsCohomologyEquiv (n : ℕ) :
    resolutionSectionCycles R (n + 1) ⧸ (resolutionSectionBoundary R n).range ≃+
      Sheaf.H.{u + 1} A (n + 1) :=
  (QuotientAddGroup.quotientAddEquivOfEq (resolutionSectionClass_ker R n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (resolutionSectionClass_surjective R (n + 1)))

/-- The exact resolution condition still needed for an affine vanishing proof. -/
theorem subsingleton_cohomology_iff_resolution_sections_exact (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} A (n + 1)) ↔
      ∀ s : resolutionSectionCycles R (n + 1),
        ∃ t : resolutionSections R n,
          resolutionSectionDifferential R n (n + 1) t = s.val := by
  constructor
  · intro h s
    exact (resolutionSectionClass_eq_zero_iff R n s).mp (h.elim _ _)
  · intro h
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨s, rfl⟩ := resolutionSectionClass_surjective R (n + 1) x
    exact (resolutionSectionClass_eq_zero_iff R n s).mpr (h s)

variable {R} {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B}

/-- A lift of a coefficient map to resolutions acts on actual global-section cycles. -/
def resolutionSectionCyclesMap (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    resolutionSectionCycles R n →+ resolutionSectionCycles S n where
  toFun s := ⟨(φ.hom.f n).hom.app (op ⊤) s.val, by
    have h := congrArg (fun g : R.cocomplex.X n ⟶ S.cocomplex.X (n + 1) ↦
      g.hom.app (op ⊤) s.val) (φ.hom.comm n (n + 1))
    change _ = (φ.hom.f (n + 1)).hom.app (op ⊤)
      (resolutionSectionDifferential R n (n + 1) s.val) at h
    rw [show resolutionSectionDifferential R n (n + 1) s.val = 0 from s.property,
      map_zero] at h
    exact h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ _ _)

/-- The resolution comparison intertwines actual coefficient maps, for any lift. -/
theorem resolutionSectionClass_naturality (φ : InjectiveResolution.Hom R S f)
    (n : ℕ) (s : resolutionSectionCycles R n) :
    Sheaf.H.map f n (resolutionSectionClass R n s) =
      resolutionSectionClass S n (resolutionSectionCyclesMap φ n s) := by
  simp only [resolutionSectionClass, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Sheaf.H.map_apply]
  rw [InjectiveResolution.extMk_comp_mk₀ _ _ _ _ φ]
  simp only [integerSheafHomEquiv_symm_comp]
  rfl

open AlgebraicGeometry.Scheme.OverField in
/-- The comparison uses precisely the pre-existing structural scalar action:
any resolution lift of the actual scalar sheaf map computes multiplication. -/
theorem module_resolutionSectionClass_smul {F : Type u} [Field F]
    (X : FScheme F) (M : X.left.Modules)
    (R : InjectiveResolution (moduleAddSheaf X.left M)) (a : F)
    (φ : InjectiveResolution.Hom R R (moduleScalar X M a))
    (n : ℕ) (s : resolutionSectionCycles R n) :
    a • (show moduleCohomology F X M n from resolutionSectionClass R n s) =
      resolutionSectionClass R n (resolutionSectionCyclesMap φ n s) :=
  resolutionSectionClass_naturality φ n s

end AlgebraicGeometry.Scheme.Cohomology
