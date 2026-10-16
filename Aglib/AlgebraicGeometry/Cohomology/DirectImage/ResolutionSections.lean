/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Native resolution sections and original module cohomology

Sections use the original module evaluation functor, followed by restriction
through the specified structural ring map. A supplied actual module injective
resolution gives its original section complex and original Ext classes.
No quasicoherence, geometric finiteness or injectivity after forgetting module
structure is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite CochainComplex HomComplex

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- Native whole-space module evaluation over the specified structural ring. -/
def moduleGlobalSectionsFunctorOfHom : X.Modules ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙ ModuleCat.restrictScalars α

/-- Top presheaf sections are naturally the original module global sections. -/
def moduleTopSectionsFunctorIso :
    moduleSectionsPresheafFunctor X α ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ≅
      moduleGlobalSectionsFunctorOfHom X α := by
  refine NatIso.ofComponents (moduleTopSectionsIso X α) ?_
  intro M N f
  ext x
  rfl

instance moduleGlobalSectionsFunctorOfHom_additive :
    (moduleGlobalSectionsFunctorOfHom X α).Additive where
  map_add := by intros; rfl

instance moduleGlobalSectionsFunctorOfHom_preservesFiniteLimits :
    PreservesFiniteLimits (moduleGlobalSectionsFunctorOfHom X α) := by
  let : (ModuleCat.restrictScalars.{u} α).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} α).isRightAdjoint
  let : PreservesFiniteLimits
      (SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op ⊤)
  exact comp_preservesFiniteLimits
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens)))
    (ModuleCat.restrictScalars.{u} α)

/-- The actual section complex of the supplied module injective resolution. -/
abbrev moduleResolutionSectionComplex {M : X.Modules} (I : InjectiveResolution M) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

/-- Native section cycles of the actual resolution. -/
abbrev moduleResolutionSectionCycles {M : X.Modules} (I : InjectiveResolution M) (n : ℤ) :=
  LinearMap.ker ((moduleResolutionSectionComplex X α I).d n (n + 1)).hom

/-- A section cycle gives its original cocycle from the actual structure module. -/
def moduleResolutionSectionCocycle {M : X.Modules} (I : InjectiveResolution M) (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) I.cochainComplex n :=
  Cocycle.fromSingleMk
    ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val)
    (zero_add _) ((n : ℤ) + 1) rfl (by
      apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).injective
      change Scheme.Modules.unitHomGlobalSectionsEquiv X _ (_ ≫ _) = 0
      rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality]
      change (I.cochainComplex.d n ((n : ℤ) + 1)).app ⊤
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _)
          ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm s.val)) = 0
      rw [AddEquiv.apply_symm_apply]
      exact s.property)

/-- Section cycles give the native structure-module Ext class of the supplied resolution. -/
def moduleResolutionSectionExtClass {M : X.Modules} (I : InjectiveResolution M) (n : ℕ) :
    moduleResolutionSectionCycles X α I n →+
      Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n where
  toFun s := I.extAddEquivCohomologyClass.symm (.mk (moduleResolutionSectionCocycle X α I n s))
  map_zero' := by
    simp only [moduleResolutionSectionCocycle, ZeroMemClass.coe_zero, map_zero,
      Cocycle.fromSingleMk_zero, CohomologyClass.mk_zero]
  map_add' s t := by
    change I.extAddEquivCohomologyClass.symm
        (.mk (moduleResolutionSectionCocycle X α I n (s + t))) = _
    have hc : moduleResolutionSectionCocycle X α I n (s + t) =
        moduleResolutionSectionCocycle X α I n s +
          moduleResolutionSectionCocycle X α I n t := by
      apply Cocycle.ext
      simp only [moduleResolutionSectionCocycle, Cocycle.fromSingleMk_coe,
        Cocycle.coe_add, Submodule.coe_add, map_add, Cochain.fromSingleMk_add]
    rw [hc, CohomologyClass.mk_add, map_add]

/-- Every native Ext class has a cycle in the original resolution section complex. -/
theorem moduleResolutionSectionExtClass_surjective {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    Function.Surjective (moduleResolutionSectionExtClass X α I n) := by
  intro x
  obtain ⟨z, rfl⟩ := I.extAddEquivCohomologyClass.symm.surjective x
  obtain ⟨c, rfl⟩ := z.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective c (n : ℤ) (zero_add _)
    ((n : ℤ) + 1) rfl
  let s := (Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)) f
  have hs : ((moduleResolutionSectionComplex X α I).d n ((n : ℤ) + 1)) s = 0 := by
    have hh := congrArg (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _) hf
    change Scheme.Modules.unitHomGlobalSectionsEquiv X _ (f ≫ _) = 0 at hh
    rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality] at hh
    exact hh
  refine ⟨⟨s, hs⟩, ?_⟩
  apply congrArg I.extAddEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  simp only [moduleResolutionSectionCocycle, Cocycle.fromSingleMk_coe, s,
    AddEquiv.symm_apply_apply]

/-- A cycle represents zero exactly when it is an actual section boundary.
The integer-indexed resolution makes this uniform in degree zero as well. -/
theorem moduleResolutionSectionExtClass_eq_zero_iff {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionExtClass X α I n s = 0 ↔
      ∃ t : (moduleResolutionSectionComplex X α I).X ((n : ℤ) - 1),
        ((moduleResolutionSectionComplex X α I).d ((n : ℤ) - 1) n) t = s.val := by
  change I.extAddEquivCohomologyClass.symm
    (.mk (moduleResolutionSectionCocycle X α I n s)) = 0 ↔ _
  rw [I.extAddEquivCohomologyClass.symm.map_eq_zero_iff, CohomologyClass.mk_eq_zero_iff,
    moduleResolutionSectionCocycle,
    Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ ((n : ℤ) - 1) (by omega)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨Scheme.Modules.unitHomGlobalSectionsAddEquiv X _ g, ?_⟩
    have hh := congrArg (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _) hg
    change Scheme.Modules.unitHomGlobalSectionsEquiv X _ (g ≫ _) =
      (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _)
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm s.val) at hh
    rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality,
      AddEquiv.apply_symm_apply] at hh
    exact hh
  · rintro ⟨t, ht⟩
    refine ⟨(Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm t, ?_⟩
    apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).injective
    change Scheme.Modules.unitHomGlobalSectionsEquiv X _ (_ ≫ _) =
      (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _)
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm s.val)
    rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality, AddEquiv.apply_symm_apply]
    change (I.cochainComplex.d ((n : ℤ) - 1) n).app ⊤
      ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _)
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm t)) = s.val
    rw [AddEquiv.apply_symm_apply]
    exact ht

/-- The original module morphism representing a section cycle in a native resolution term. -/
def moduleResolutionSectionHom {M : X.Modules} (I : InjectiveResolution M) (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ I.cocomplex.X n :=
  (Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val ≫
    (I.cochainComplexXIso n n rfl).hom

/-- The represented original module morphism is a cocycle of the native resolution. -/
theorem moduleResolutionSectionHom_comp_d {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionHom X α I n s ≫ I.cocomplex.d n (n + 1) = 0 := by
  apply (cancel_mono (I.cochainComplexXIso (n + 1) (n + 1) rfl).inv).mp
  simp only [moduleResolutionSectionHom, Category.assoc, zero_comp,
    ← I.cochainComplex_d n (n + 1) n (n + 1) rfl rfl]
  apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).injective
  change Scheme.Modules.unitHomGlobalSectionsEquiv X _ (_ ≫ _) = 0
  rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality]
  change (I.cochainComplex.d n ((n : ℤ) + 1)).app ⊤
    ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _)
      ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm s.val)) = 0
  rw [AddEquiv.apply_symm_apply]
  exact s.property

/-- The cycle map is exactly the native `extMk` of its original representing morphism. -/
theorem moduleResolutionSectionExtClass_eq_extMk {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionExtClass X α I n s =
      I.extMk (moduleResolutionSectionHom X α I n s) (n + 1) rfl
        (moduleResolutionSectionHom_comp_d X α I n s) := by
  apply congrArg I.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  simp only [moduleResolutionSectionCocycle, moduleResolutionSectionHom,
    Cocycle.fromSingleMk_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem unitHomGlobalSectionsAddEquiv_symm_smul (P : X.Modules) (a : Γ(X, ⊤))
    (s : Γ(P, ⊤)) :
    (Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).symm (a • s) =
      Scheme.Modules.unitMul X a ≫
        (Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).symm s := by
  let f : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ P :=
    (Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).symm s
  apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).injective
  rw [AddEquiv.apply_symm_apply]
  change a • s = Scheme.Modules.Hom.app f ⊤
    (Scheme.Modules.Hom.app (Scheme.Modules.unitMul X a) ⊤ (1 : Γ(X, ⊤)))
  rw [Scheme.Modules.unitMul_app]
  change a • s = Scheme.Modules.Hom.app f ⊤ (1 * globalRestriction X ⊤ a)
  rw [globalRestriction_top_apply, one_mul]
  symm
  calc
    _ = a • Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤)) := by
      simpa only [smul_eq_mul, mul_one] using
        Scheme.Modules.Hom.app_smul f a (1 : Γ(X, ⊤))
    _ = a • s := by
      change a • (Scheme.Modules.unitHomGlobalSectionsAddEquiv X P)
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).symm s) = a • s
      rw [AddEquiv.apply_symm_apply]

/-- Structural multiplication on section cycles is original source multiplication. -/
theorem moduleResolutionSectionHom_smul {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (r : R) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionHom X α I n (r • s) =
      Scheme.Modules.unitMul X (α r) ≫ moduleResolutionSectionHom X α I n s := by
  dsimp only [moduleResolutionSectionHom]
  change (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm
    (α r • (show Γ(I.cochainComplex.X n, ⊤) from s.val)) ≫ _ = _
  rw [unitHomGlobalSectionsAddEquiv_symm_smul, Category.assoc]

/-- The original resolution Ext class preserves the specified structural ring action. -/
theorem moduleResolutionSectionExtClass_smul {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (r : R) (s : moduleResolutionSectionCycles X α I n) :
    let := moduleExtModuleOfHom X α M n
    moduleResolutionSectionExtClass X α I n (r • s) =
      r • moduleResolutionSectionExtClass X α I n s := by
  let := moduleExtModuleOfHom X α M n
  change moduleResolutionSectionExtClass X α I n (r • s) =
    (Ext.mk₀ (Scheme.Modules.unitMul X (α r))).comp
      (moduleResolutionSectionExtClass X α I n s) (Nat.zero_add n)
  rw [moduleResolutionSectionExtClass_eq_extMk, moduleResolutionSectionExtClass_eq_extMk,
    InjectiveResolution.mk₀_comp_extMk]
  congr 1
  exact moduleResolutionSectionHom_smul X α I n r s

/-- Actual section cycles map linearly to the unchanged additive-sheaf cohomology. -/
def moduleResolutionSectionClass {M : X.Modules} (I : InjectiveResolution M) (n : ℕ) :
    let := moduleCohomologyModuleOfHom X α M n
    moduleResolutionSectionCycles X α I n →ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  let := moduleExtModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom X α M n
  let c : moduleResolutionSectionCycles X α I n →ₗ[R]
      Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n := {
    __ := moduleResolutionSectionExtClass X α I n
    map_smul' := fun r s => moduleResolutionSectionExtClass_smul X α I n r s }
  exact (moduleExtCohomologyLinearEquiv X α M n).toLinearMap.comp c

/-- The linear class map retains the original Ext class and original forgetting map. -/
theorem moduleResolutionSectionClass_apply {M : X.Modules} (I : InjectiveResolution M)
    (n : ℕ) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionClass X α I n s =
      moduleExtCohomologyMap X M n (moduleResolutionSectionExtClass X α I n s) := rfl

/-- The original cohomology class map is surjective for every supplied resolution. -/
theorem moduleResolutionSectionClass_surjective {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    Function.Surjective (moduleResolutionSectionClass X α I n) :=
  (moduleExtCohomologyMap_bijective X M n).2.comp
    (moduleResolutionSectionExtClass_surjective X α I n)

/-- The original cohomology class vanishes exactly on actual section boundaries. -/
theorem moduleResolutionSectionClass_eq_zero_iff {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionClass X α I n s = 0 ↔
      ∃ t : (moduleResolutionSectionComplex X α I).X ((n : ℤ) - 1),
        ((moduleResolutionSectionComplex X α I).d ((n : ℤ) - 1) n) t = s.val := by
  change (moduleExtCohomologyAddEquiv X M n)
    (moduleResolutionSectionExtClass X α I n s) = 0 ↔ _
  rw [(moduleExtCohomologyAddEquiv X M n).map_eq_zero_iff,
    moduleResolutionSectionExtClass_eq_zero_iff]

/-- The kernel is precisely the native incoming-differential range in the cycle module. -/
theorem moduleResolutionSectionClass_ker {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    let := moduleCohomologyModuleOfHom X α M n
    let K := moduleResolutionSectionComplex X α I
    LinearMap.ker (moduleResolutionSectionClass X α I n) =
      LinearMap.range (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatToCycles := by
  let := moduleCohomologyModuleOfHom X α M n
  ext s
  rw [LinearMap.mem_ker, moduleResolutionSectionClass_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, congrArg Subtype.val ht⟩

/-- Native homology data identify resolution-section homology with its actual cycle quotient. -/
def moduleResolutionSectionHomologyIso {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    let K := moduleResolutionSectionComplex X α I
    K.homology (n : ℤ) ≅ (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.H := by
  let K := moduleResolutionSectionComplex X α I
  exact K.homologyIsoSc' ((n : ℤ) - 1) n ((n : ℤ) + 1) (by simp) (by simp) ≪≫
    (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatHomologyIso

/-- Native homology of the original module resolution's sections computes unchanged
additive cohomology linearly for the specified structural ring action. -/
def moduleResolutionSectionsCohomologyLinearEquiv {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    let := moduleCohomologyModuleOfHom X α M n
    (moduleResolutionSectionComplex X α I).homology (n : ℤ) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  let := moduleCohomologyModuleOfHom X α M n
  let K := moduleResolutionSectionComplex X α I
  let q : (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.H ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
    (Submodule.quotEquivOfEq _ _ (moduleResolutionSectionClass_ker X α I n).symm).trans
      ((moduleResolutionSectionClass X α I n).quotKerEquivOfSurjective
        (moduleResolutionSectionClass_surjective X α I n))
  exact (moduleResolutionSectionHomologyIso X α I n).toLinearEquiv.trans q

/-- On the native quotient representative the comparison is the original Ext class map. -/
theorem moduleResolutionSectionsCohomologyLinearEquiv_apply_mk {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionsCohomologyLinearEquiv X α I n
        ((moduleResolutionSectionHomologyIso X α I n).inv (Submodule.Quotient.mk s)) =
      moduleResolutionSectionClass X α I n s := by
  let := moduleCohomologyModuleOfHom X α M n
  change ((Submodule.quotEquivOfEq _ _ (moduleResolutionSectionClass_ker X α I n).symm).trans
      ((moduleResolutionSectionClass X α I n).quotKerEquivOfSurjective
        (moduleResolutionSectionClass_surjective X α I n)))
    ((moduleResolutionSectionHomologyIso X α I n).toLinearEquiv
      ((moduleResolutionSectionHomologyIso X α I n).toLinearEquiv.symm
        (Submodule.Quotient.mk s))) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk (moduleResolutionSectionClass X α I n)
    (moduleResolutionSectionClass_surjective X α I n) s

end AlgebraicGeometry.Scheme.Cohomology
