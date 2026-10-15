/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open.Basic

/-!
# Original module-open Ext classes of actual section cycles

The original open-free section equivalence sends each actual section cycle
to its original cocycle in the supplied module resolution. Its native Ext
class vanishes exactly on actual section boundaries, including degree zero.
Structural scalars agree with Mathlib's native module Ext scalar action.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite CochainComplex HomComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (U : X.Opens)

/-- The original section cycle gives its original module-open cocycle. -/
def moduleResolutionOpenSectionCocycle {M : X.Modules} (I : InjectiveResolution M) (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj (Scheme.Modules.openFree X U))
      I.cochainComplex n :=
  Cocycle.fromSingleMk
    ((Scheme.Modules.openFreeHomAddEquiv X U (I.cochainComplex.X n)).symm s.val)
    (zero_add _) ((n : ℤ) + 1) rfl (by
      apply (Scheme.Modules.openFreeHomAddEquiv X U _).injective
      change Scheme.Modules.openFreeHomEquiv X U _ (_ ≫ _) = 0
      rw [Scheme.Modules.openFreeHomEquiv_comp]
      change (I.cochainComplex.d n ((n : ℤ) + 1)).app U
        ((Scheme.Modules.openFreeHomAddEquiv X U _)
          ((Scheme.Modules.openFreeHomAddEquiv X U _).symm s.val)) = 0
      rw [AddEquiv.apply_symm_apply]
      exact s.property)

/-- The actual section cycle represents the native Ext class of the supplied module resolution. -/
def moduleResolutionOpenSectionExtClass {M : X.Modules} (I : InjectiveResolution M) (n : ℕ) :
    moduleResolutionOpenSectionCycles X α U I n →+
      Ext.{u + 1} (Scheme.Modules.openFree X U) M n where
  toFun s := I.extAddEquivCohomologyClass.symm
    (.mk (moduleResolutionOpenSectionCocycle X α U I n s))
  map_zero' := by
    simp only [moduleResolutionOpenSectionCocycle, ZeroMemClass.coe_zero, map_zero,
      Cocycle.fromSingleMk_zero, CohomologyClass.mk_zero]
  map_add' s t := by
    change I.extAddEquivCohomologyClass.symm
        (.mk (moduleResolutionOpenSectionCocycle X α U I n (s + t))) = _
    have hc : moduleResolutionOpenSectionCocycle X α U I n (s + t) =
        moduleResolutionOpenSectionCocycle X α U I n s +
          moduleResolutionOpenSectionCocycle X α U I n t := by
      apply Cocycle.ext
      simp only [moduleResolutionOpenSectionCocycle, Cocycle.fromSingleMk_coe,
        Cocycle.coe_add, Submodule.coe_add, map_add, Cochain.fromSingleMk_add]
    rw [hc, CohomologyClass.mk_add, map_add]

theorem moduleResolutionOpenSectionExtClass_surjective {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    Function.Surjective (moduleResolutionOpenSectionExtClass X α U I n) := by
  intro x
  obtain ⟨z, rfl⟩ := I.extAddEquivCohomologyClass.symm.surjective x
  obtain ⟨c, rfl⟩ := z.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective c (n : ℤ) (zero_add _)
    ((n : ℤ) + 1) rfl
  let s := (Scheme.Modules.openFreeHomAddEquiv X U (I.cochainComplex.X n)) f
  have hs : ((moduleResolutionOpenSectionComplex X α U I).d n ((n : ℤ) + 1)) s = 0 := by
    have hh := congrArg (Scheme.Modules.openFreeHomAddEquiv X U _) hf
    change Scheme.Modules.openFreeHomEquiv X U _ (f ≫ _) = 0 at hh
    rw [Scheme.Modules.openFreeHomEquiv_comp] at hh
    exact hh
  refine ⟨⟨s, hs⟩, ?_⟩
  apply congrArg I.extAddEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  simp only [moduleResolutionOpenSectionCocycle, Cocycle.fromSingleMk_coe, s,
    AddEquiv.symm_apply_apply]

/-- The original Ext class is zero exactly on actual section boundaries, in every degree. -/
theorem moduleResolutionOpenSectionExtClass_eq_zero_iff {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionExtClass X α U I n s = 0 ↔
      ∃ t : (moduleResolutionOpenSectionComplex X α U I).X ((n : ℤ) - 1),
        ((moduleResolutionOpenSectionComplex X α U I).d ((n : ℤ) - 1) n) t = s.val := by
  change I.extAddEquivCohomologyClass.symm
    (.mk (moduleResolutionOpenSectionCocycle X α U I n s)) = 0 ↔ _
  rw [I.extAddEquivCohomologyClass.symm.map_eq_zero_iff, CohomologyClass.mk_eq_zero_iff,
    moduleResolutionOpenSectionCocycle,
    Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ ((n : ℤ) - 1) (by omega)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨Scheme.Modules.openFreeHomAddEquiv X U _ g, ?_⟩
    have hh := congrArg (Scheme.Modules.openFreeHomAddEquiv X U _) hg
    change Scheme.Modules.openFreeHomEquiv X U _ (g ≫ _) =
      (Scheme.Modules.openFreeHomAddEquiv X U _)
        ((Scheme.Modules.openFreeHomAddEquiv X U _).symm s.val) at hh
    rw [Scheme.Modules.openFreeHomEquiv_comp, AddEquiv.apply_symm_apply] at hh
    exact hh
  · rintro ⟨t, ht⟩
    refine ⟨(Scheme.Modules.openFreeHomAddEquiv X U _).symm t, ?_⟩
    apply (Scheme.Modules.openFreeHomAddEquiv X U _).injective
    change Scheme.Modules.openFreeHomEquiv X U _ (_ ≫ _) =
      (Scheme.Modules.openFreeHomAddEquiv X U _)
        ((Scheme.Modules.openFreeHomAddEquiv X U _).symm s.val)
    rw [Scheme.Modules.openFreeHomEquiv_comp, AddEquiv.apply_symm_apply]
    change (I.cochainComplex.d ((n : ℤ) - 1) n).app U
      ((Scheme.Modules.openFreeHomAddEquiv X U _)
        ((Scheme.Modules.openFreeHomAddEquiv X U _).symm t)) = s.val
    rw [AddEquiv.apply_symm_apply]
    exact ht

/-- The original open-free morphism representing a cycle in the native resolution term. -/
def moduleResolutionOpenSectionHom {M : X.Modules} (I : InjectiveResolution M) (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    Scheme.Modules.openFree X U ⟶ I.cocomplex.X n :=
  (Scheme.Modules.openFreeHomAddEquiv X U (I.cochainComplex.X n)).symm s.val ≫
    (I.cochainComplexXIso n n rfl).hom

theorem moduleResolutionOpenSectionHom_comp_d {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionHom X α U I n s ≫ I.cocomplex.d n (n + 1) = 0 := by
  apply (cancel_mono (I.cochainComplexXIso (n + 1) (n + 1) rfl).inv).mp
  simp only [moduleResolutionOpenSectionHom, Category.assoc, zero_comp,
    ← I.cochainComplex_d n (n + 1) n (n + 1) rfl rfl]
  apply (Scheme.Modules.openFreeHomAddEquiv X U _).injective
  change Scheme.Modules.openFreeHomEquiv X U _ (_ ≫ _) = 0
  rw [Scheme.Modules.openFreeHomEquiv_comp]
  change (I.cochainComplex.d n ((n : ℤ) + 1)).app U
    ((Scheme.Modules.openFreeHomAddEquiv X U _)
      ((Scheme.Modules.openFreeHomAddEquiv X U _).symm s.val)) = 0
  rw [AddEquiv.apply_symm_apply]
  exact s.property

/-- The forward class map is exactly the native `extMk` on its original representing morphism. -/
theorem moduleResolutionOpenSectionExtClass_eq_extMk {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionExtClass X α U I n s =
      I.extMk (moduleResolutionOpenSectionHom X α U I n s) (n + 1) rfl
        (moduleResolutionOpenSectionHom_comp_d X α U I n s) := by
  apply congrArg I.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  simp only [moduleResolutionOpenSectionCocycle, moduleResolutionOpenSectionHom,
    Cocycle.fromSingleMk_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem openFreeHomAddEquiv_symm_smul (P : X.Modules) (r : R)
    (s : (moduleSectionsPresheaf X α P).obj (op U)) :
    (Scheme.Modules.openFreeHomAddEquiv X U P).symm (r • s) =
      Scheme.Modules.globalScalarEndomorphism X (Scheme.Modules.openFree X U) (α r) ≫
        (Scheme.Modules.openFreeHomAddEquiv X U P).symm s := by
  let f : Scheme.Modules.openFree X U ⟶ P :=
    (Scheme.Modules.openFreeHomAddEquiv X U P).symm s
  have hn :
      Scheme.Modules.globalScalarEndomorphism X (Scheme.Modules.openFree X U) (α r) ≫ f =
        f ≫ Scheme.Modules.globalScalarEndomorphism X P (α r) :=
    ((Scheme.Modules.globalScalarCenter X (α r)).naturality f).symm
  apply (Scheme.Modules.openFreeHomAddEquiv X U P).injective
  rw [AddEquiv.apply_symm_apply]
  change r • s = Scheme.Modules.openFreeHomEquiv X U P
    (Scheme.Modules.globalScalarEndomorphism X (Scheme.Modules.openFree X U) (α r) ≫ f)
  rw [hn, Scheme.Modules.openFreeHomEquiv_comp]
  change r • s = (Scheme.Modules.globalScalarEndomorphism X P (α r)).val.app (op U)
    ((Scheme.Modules.openFreeHomAddEquiv X U P)
      ((Scheme.Modules.openFreeHomAddEquiv X U P).symm s))
  rw [AddEquiv.apply_symm_apply, Scheme.Modules.globalScalarEndomorphism_app]
  rfl

/-- The original cycle morphism preserves structural multiplication by original source scalars. -/
theorem moduleResolutionOpenSectionHom_smul {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (r : R) (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionHom X α U I n (r • s) =
      Scheme.Modules.globalScalarEndomorphism X (Scheme.Modules.openFree X U) (α r) ≫
        moduleResolutionOpenSectionHom X α U I n s := by
  dsimp only [moduleResolutionOpenSectionHom]
  change (Scheme.Modules.openFreeHomAddEquiv X U _).symm (r • s.val) ≫ _ = _
  rw [openFreeHomAddEquiv_symm_smul, Category.assoc]

/-- The original resolution Ext class has the existing native linear-category scalar action. -/
theorem moduleResolutionOpenSectionExtClass_smul {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (r : R) (s : moduleResolutionOpenSectionCycles X α U I n) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom X α
    moduleResolutionOpenSectionExtClass X α U I n (r • s) =
      r • moduleResolutionOpenSectionExtClass X α U I n s := by
  let := Scheme.Modules.moduleCategoryLinearOfHom X α
  rw [moduleExt_smul_precomp_of_hom X α (Scheme.Modules.openFree X U) M n r]
  rw [moduleResolutionOpenSectionExtClass_eq_extMk,
    moduleResolutionOpenSectionExtClass_eq_extMk, InjectiveResolution.mk₀_comp_extMk]
  congr 1
  exact moduleResolutionOpenSectionHom_smul X α U I n r s

end AlgebraicGeometry.Scheme.Cohomology
