/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Comparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGammaNaturality

/-!
# Native derived module sections and original abelian cohomology

The left hand side derives actual terminal evaluation, with actual scalar
restriction for a coefficient action. The right hand side is original
`Sheaf.H`. The comparison is obtained from genuine injective acyclicity,
not from an assumed comparison or acyclicity premise.
-/

@[expose] public noncomputable section

universe u v eM eA s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- Compose two already normalized additive comparisons without unfolding either one. -/
theorem comparisonTrans_naturality
    {A B C D E F : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (e₁ : A ≃+ B) (e₂ : B ≃+ C) (e₁' : D ≃+ E) (e₂' : E ≃+ F)
    (f : A → D) (g : B → E) (h : C → F) (x : A)
    (h₁ : e₁' (f x) = g (e₁ x)) (h₂ : e₂' (g (e₁ x)) = h (e₂ (e₁ x))) :
    (e₁'.trans e₂') (f x) = h ((e₁.trans e₂) x) :=
  (congrArg e₂' h₁).trans h₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

section SmallScalars

variable (R : Sheaf J RingCat.{v})
  [HasExt.{eM} (SheafOfModules.{max u v} R)]

local instance : EnoughInjectives (SheafOfModules.{max u v} R) :=
  SheafOfModules.enoughInjectivesLargeOverSmallScalars.{u, v, 0, v} R

/-- The existing acyclicity theorem also applies to the native Γ comparison's
chosen universe lift of the rank-one module. The scalar ring is unchanged. -/
def alignedModuleExtCohomologyAddEquiv
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    Ext.{eM} (SheafOfModules.liftedUnit.{u, v, max u v, v} R) M n ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  AddEquiv.ofBijective (cohomologyMap.{u, v, v, max u v, eM, eA} hT R M n)
    ((SheafOfModules.toSheaf R).extPrecompMap_bijective_of_acyclic_injectives
      (liftedUnitIntegerMap.{u, v, v, max u v} hT R)
      (cohomologyMap_bijective_zero.{u, v, v, max u v, eM, eA} hT R)
      (fun I _ q => toSheaf_injective_cohomology_subsingleton R I hT q) M n)

/-- Actual derived terminal sections equal original abelian sheaf cohomology. -/
def derivedTerminalCohomologyAddEquiv
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    ((SheafOfModules.evaluation R (op T)).rightDerived n).obj M ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  (derivedTerminalSectionsExtAddEquiv.{u, v, v, 0, eM} hT R M n).trans
    (alignedModuleExtCohomologyAddEquiv hT R M n)

/-- Native terminal-section coefficient maps agree with original abelian cohomology maps. -/
theorem derivedTerminalCohomologyAddEquiv_naturality
    {M N : SheafOfModules.{max u v} R} (f : M ⟶ N) (n : ℕ)
    (x : ((SheafOfModules.evaluation R (op T)).rightDerived n).obj M) :
    derivedTerminalCohomologyAddEquiv hT R N n
        (((SheafOfModules.evaluation R (op T)).rightDerived n).map f x) =
      Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n
        (derivedTerminalCohomologyAddEquiv hT R M n x) :=
  (congrArg (cohomologyMap.{u, v, v, max u v, eM, eA} hT R N n)
    (derivedTerminalSectionsExtAddEquiv_naturality.{u, v, v, 0, eM} hT R f n x)).trans
      (cohomologyMap_naturality.{u, v, v, max u v, eM, eA} hT R f n _)

variable (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))

/-- Actual coefficient-valued derived sections equal original abelian cohomology. -/
def derivedScalarCohomologyAddEquiv
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    ((scalarTerminalSections.{u, v, v, 0} R Λ α).rightDerived n).obj M ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  (derivedScalarTerminalSectionsExtAddEquiv.{u, v, v, 0, eM} hT R Λ α M n).trans
    (alignedModuleExtCohomologyAddEquiv hT R M n)

/-- The comparison intertwines the original coefficient maps. -/
theorem derivedScalarCohomologyAddEquiv_naturality
    {M N : SheafOfModules.{max u v} R} (f : M ⟶ N) (n : ℕ)
    (x : ((scalarTerminalSections.{u, v, v, 0} R Λ α).rightDerived n).obj M) :
    derivedScalarCohomologyAddEquiv hT R Λ α N n
        (((scalarTerminalSections.{u, v, v, 0, s} R Λ α).rightDerived n).map f x) =
      Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n
        (derivedScalarCohomologyAddEquiv hT R Λ α M n x) := by
  unfold derivedScalarCohomologyAddEquiv
  exact comparisonTrans_naturality
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, v, 0, eM, s} hT R Λ α M n)
    (alignedModuleExtCohomologyAddEquiv hT R M n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, v, 0, eM, s} hT R Λ α N n)
    (alignedModuleExtCohomologyAddEquiv hT R N n)
    (((scalarTerminalSections.{u, v, v, 0, s} R Λ α).rightDerived n).map f)
    (fun z => z.comp (Ext.mk₀ f) (Nat.add_zero n))
    (Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n) x
    (derivedScalarTerminalSectionsExtAddEquiv_naturality.{u, v, v, 0, eM, s}
      hT R Λ α f n x)
    (cohomologyMap_naturality.{u, v, v, max u v, eM, eA} hT R f n _)


end SmallScalars

section LargeScalars

variable (R : Sheaf J RingCat.{max u v})
  [HasExt.{eM} (SheafOfModules.{max u v} R)]

local instance : EnoughInjectives (SheafOfModules.{max u v} R) :=
  SheafOfModules.enoughInjectivesLarge.{u, v, 0} R

/-- Actual derived terminal sections equal original abelian sheaf cohomology. -/
def derivedTerminalCohomologyAddEquivLargeScalars
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    ((SheafOfModules.evaluation R (op T)).rightDerived n).obj M ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  (derivedTerminalSectionsExtAddEquiv.{u, v, max u v, 0, eM} hT R M n).trans
    (moduleExtCohomologyAddEquivLargeScalars hT R M n)

/-- Native terminal-section coefficient maps agree with original abelian cohomology maps. -/
theorem derivedTerminalCohomologyAddEquiv_largeScalars_naturality
    {M N : SheafOfModules.{max u v} R} (f : M ⟶ N) (n : ℕ)
    (x : ((SheafOfModules.evaluation R (op T)).rightDerived n).obj M) :
    derivedTerminalCohomologyAddEquivLargeScalars hT R N n
        (((SheafOfModules.evaluation R (op T)).rightDerived n).map f x) =
      Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n
        (derivedTerminalCohomologyAddEquivLargeScalars hT R M n x) :=
  (congrArg (cohomologyMap.{u, v, max u v, max u v, eM, eA} hT R N n)
    (derivedTerminalSectionsExtAddEquiv_naturality.{u, v, max u v, 0, eM} hT R f n x)).trans
      (cohomologyMap_naturality.{u, v, max u v, max u v, eM, eA} hT R f n _)

variable (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))

/-- Actual coefficient-valued derived sections equal original abelian cohomology. -/
def derivedScalarCohomologyAddEquivLargeScalars
    (M : SheafOfModules.{max u v} R) (n : ℕ) :
    ((scalarTerminalSections.{u, v, max u v, 0} R Λ α).rightDerived n).obj M ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  (derivedScalarTerminalSectionsExtAddEquiv.{u, v, max u v, 0, eM} hT R Λ α M n).trans
    (moduleExtCohomologyAddEquivLargeScalars hT R M n)

/-- The comparison intertwines the original coefficient maps. -/
theorem derivedScalarCohomologyAddEquiv_largeScalars_naturality
    {M N : SheafOfModules.{max u v} R} (f : M ⟶ N) (n : ℕ)
    (x : ((scalarTerminalSections.{u, v, max u v, 0} R Λ α).rightDerived n).obj M) :
    derivedScalarCohomologyAddEquivLargeScalars hT R Λ α N n
        (((scalarTerminalSections.{u, v, max u v, 0, s} R Λ α).rightDerived n).map f x) =
      Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n
        (derivedScalarCohomologyAddEquivLargeScalars hT R Λ α M n x) := by
  unfold derivedScalarCohomologyAddEquivLargeScalars
  exact comparisonTrans_naturality
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, max u v, 0, eM, s} hT R Λ α M n)
    (moduleExtCohomologyAddEquivLargeScalars hT R M n)
    (derivedScalarTerminalSectionsExtAddEquiv.{u, v, max u v, 0, eM, s} hT R Λ α N n)
    (moduleExtCohomologyAddEquivLargeScalars hT R N n)
    (((scalarTerminalSections.{u, v, max u v, 0, s} R Λ α).rightDerived n).map f)
    (fun z => z.comp (Ext.mk₀ f) (Nat.add_zero n))
    (Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n) x
    (derivedScalarTerminalSectionsExtAddEquiv_naturality.{u, v, max u v, 0, eM, s}
      hT R Λ α f n x)
    (cohomologyMap_naturality.{u, v, max u v, max u v, eM, eA} hT R f n _)


end LargeScalars

section Constant

variable [HasSheafify J RingCat.{v}] (Λ : RingCat.{v})
  [HasExt.{eM} (SheafOfModules.{max u v} ((constantSheaf J RingCat).obj Λ))]

local instance : EnoughInjectives
    (SheafOfModules.{max u v} ((constantSheaf J RingCat).obj Λ)) :=
  SheafOfModules.enoughInjectivesLargeOverSmallScalars.{u, v, 0, v} _

/-- Constant coefficients use the native constant-sheaf unit, without invertibility assumptions. -/
def constantDerivedCohomologyAddEquiv
    (M : SheafOfModules.{max u v} ((constantSheaf J RingCat).obj Λ)) (n : ℕ) :
    ((constantTerminalSections.{u, v, v, 0} (J := J) hT Λ).rightDerived n).obj M ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf _).obj M) n :=
  derivedScalarCohomologyAddEquiv hT _ Λ (constantTerminalScalarHom (J := J) hT Λ) M n

end Constant

section ConstantLarge

variable [HasSheafify J RingCat.{max u v}] (Λ : RingCat.{max u v})
  [HasExt.{eM} (SheafOfModules.{max u v} ((constantSheaf J RingCat).obj Λ))]

local instance : EnoughInjectives
    (SheafOfModules.{max u v} ((constantSheaf J RingCat).obj Λ)) :=
  SheafOfModules.enoughInjectivesLarge.{u, v, 0} _

/-- Large-valued constant coefficients also use their original coefficient action. -/
def constantDerivedCohomologyAddEquivLargeScalars
    (M : SheafOfModules.{max u v} ((constantSheaf J RingCat).obj Λ)) (n : ℕ) :
    ((constantTerminalSections.{u, v, max u v, 0} (J := J) hT Λ).rightDerived n).obj M ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf _).obj M) n :=
  derivedScalarCohomologyAddEquivLargeScalars hT _ Λ
    (constantTerminalScalarHom (J := J) hT Λ) M n

end ConstantLarge

end CategoryTheory.Sheaf.ModuleCoefficients
