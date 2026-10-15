/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections

/-! # Coefficient naturality of native resolution sections

An actual lift between the supplied module injective resolutions gives its
original map of section cycles. The comparison with unchanged additive
cohomology preserves that lift and the original coefficient arrow.
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
  {M N : X.Modules} (I : InjectiveResolution M) (J : InjectiveResolution N)
  {f : M ⟶ N} (φ : InjectiveResolution.Hom I J f)

/-- The actual lifted coefficient map on native resolution-section cycles. -/
def moduleResolutionSectionCyclesMap (n : ℕ) :
    moduleResolutionSectionCycles X α I n →ₗ[R]
      moduleResolutionSectionCycles X α J n := by
  let a := ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map φ.hom'
  refine {
    toFun := fun s => ⟨a.f n s.val, ?_⟩
    map_add' := fun s t => Subtype.ext ((a.f n).hom.map_add _ _)
    map_smul' := fun r s => Subtype.ext ((a.f n).hom.map_smul _ _) }
  have h := congrArg
    (fun g : (moduleResolutionSectionComplex X α I).X n ⟶
        (moduleResolutionSectionComplex X α J).X ((n : ℤ) + 1) => g s.val)
    (a.comm n ((n : ℤ) + 1))
  change _ = a.f ((n : ℤ) + 1)
    (((moduleResolutionSectionComplex X α I).d n ((n : ℤ) + 1)) s.val) at h
  rw [s.property, map_zero] at h
  exact h

/-- The lift acts by its original component on actual whole-space sections. -/
theorem moduleResolutionSectionCyclesMap_apply (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    (moduleResolutionSectionCyclesMap X α I J φ n s).val =
      Scheme.Modules.Hom.app (φ.hom'.f n) ⊤ s.val := rfl

/-- The representing module morphisms retain the actual resolution-lift square. -/
theorem moduleResolutionSectionHom_naturality (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionHom X α J n (moduleResolutionSectionCyclesMap X α I J φ n s) =
      moduleResolutionSectionHom X α I n s ≫ φ.hom.f n := by
  have h :
      (Scheme.Modules.unitHomGlobalSectionsAddEquiv X (J.cochainComplex.X n)).symm
          (Scheme.Modules.Hom.app (φ.hom'.f n) ⊤ s.val) =
        (Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val ≫
          φ.hom'.f n := by
    apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).injective
    rw [AddEquiv.apply_symm_apply]
    change _ = Scheme.Modules.unitHomGlobalSectionsEquiv X _ (_ ≫ _)
    rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality]
    change Scheme.Modules.Hom.app (φ.hom'.f n) ⊤ s.val =
      Scheme.Modules.Hom.app (φ.hom'.f n) ⊤
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _)
          ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm s.val))
    rw [AddEquiv.apply_symm_apply]
  dsimp only [moduleResolutionSectionHom]
  change (Scheme.Modules.unitHomGlobalSectionsAddEquiv X _).symm
      (Scheme.Modules.Hom.app (φ.hom'.f n) ⊤ s.val) ≫ _ = _
  rw [h, φ.hom'_f n n rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original additive cohomology coefficient map agrees with the actual lifted cycle map. -/
theorem moduleResolutionSectionClass_naturality (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    moduleCohomologyMapOfHom X α f n (moduleResolutionSectionClass X α I n s) =
      moduleResolutionSectionClass X α J n (moduleResolutionSectionCyclesMap X α I J φ n s) := by
  change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f) n
      (moduleExtCohomologyMap X M n (moduleResolutionSectionExtClass X α I n s)) =
    moduleExtCohomologyMap X N n
      (moduleResolutionSectionExtClass X α J n (moduleResolutionSectionCyclesMap X α I J φ n s))
  rw [← moduleExtCohomologyMap_naturality X f n]
  apply congrArg (moduleExtCohomologyMap X N n)
  rw [moduleResolutionSectionExtClass_eq_extMk, moduleResolutionSectionExtClass_eq_extMk,
    InjectiveResolution.extMk_comp_mk₀ _ _ _ _ φ]
  congr 1
  exact (moduleResolutionSectionHom_naturality X α I J φ n s).symm

/-- Native abstract cycles are the original kernel of the section differential. -/
def moduleResolutionSectionCyclesIso (n : ℕ) :
    (moduleResolutionSectionComplex X α I).cycles (n : ℤ) ≅
      ModuleCat.of R (moduleResolutionSectionCycles X α I n) :=
  (moduleResolutionSectionComplex X α I).cyclesIsoSc'
      ((n : ℤ) - 1) n ((n : ℤ) + 1) (by simp) (by simp) ≪≫
    ((moduleResolutionSectionComplex X α I).sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatCyclesIso

/-- The native cycle comparison keeps the original section in the resolution term. -/
theorem moduleResolutionSectionCyclesIso_hom_val (n : ℕ)
    (c : (moduleResolutionSectionComplex X α I).cycles (n : ℤ)) :
    ((moduleResolutionSectionCyclesIso X α I n).hom c).val =
      (moduleResolutionSectionComplex X α I).iCycles n c := by
  let K := moduleResolutionSectionComplex X α I
  have h : (moduleResolutionSectionCyclesIso X α I n).hom ≫
      (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.i = K.iCycles n := by
    dsimp only [moduleResolutionSectionCyclesIso, Iso.trans_hom]
    rw [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  exact congrArg (fun k => k c) h

/-- The native homology comparison preserves the original cycle projection. -/
theorem moduleResolutionSectionHomologyIso_π (n : ℕ) :
    let K := moduleResolutionSectionComplex X α I
    K.homologyπ n ≫ (moduleResolutionSectionHomologyIso X α I n).hom =
      (moduleResolutionSectionCyclesIso X α I n).hom ≫
        (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.π := by
  dsimp only [moduleResolutionSectionHomologyIso, moduleResolutionSectionCyclesIso,
    Iso.trans_hom]
  rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom, Category.assoc,
    ShortComplex.π_moduleCatCyclesIso_hom]
  rw [Category.assoc]

/-- The comparison sends the original abstract cycle class to its original Ext class. -/
theorem moduleResolutionSectionsCohomologyLinearEquiv_homologyπ (n : ℕ)
    (c : (moduleResolutionSectionComplex X α I).cycles (n : ℤ)) :
    moduleResolutionSectionsCohomologyLinearEquiv X α I n
        ((moduleResolutionSectionComplex X α I).homologyπ n c) =
      moduleResolutionSectionClass X α I n
        ((moduleResolutionSectionCyclesIso X α I n).hom c) := by
  let K := moduleResolutionSectionComplex X α I
  let e := moduleResolutionSectionHomologyIso X α I n
  have h := congrArg (fun k => k c) (moduleResolutionSectionHomologyIso_π X α I n)
  change e.hom (K.homologyπ n c) =
    Submodule.Quotient.mk ((moduleResolutionSectionCyclesIso X α I n).hom c) at h
  have h' : K.homologyπ n c =
      e.inv (Submodule.Quotient.mk ((moduleResolutionSectionCyclesIso X α I n).hom c)) := by
    apply e.toLinearEquiv.injective
    change e.toLinearEquiv (K.homologyπ n c) = e.toLinearEquiv
      (e.toLinearEquiv.symm
        (Submodule.Quotient.mk ((moduleResolutionSectionCyclesIso X α I n).hom c)))
    rw [LinearEquiv.apply_symm_apply]
    exact h
  rw [h']
  exact moduleResolutionSectionsCohomologyLinearEquiv_apply_mk X α I n _

/-- The linear cohomology comparison preserves every original coefficient-resolution lift. -/
theorem moduleResolutionSectionsCohomologyLinearEquiv_naturality (n : ℕ)
    (x : (moduleResolutionSectionComplex X α I).homology (n : ℤ)) :
    let a := ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map φ.hom'
    moduleResolutionSectionsCohomologyLinearEquiv X α J n
        (HomologicalComplex.homologyMap a (n : ℤ) x) =
      moduleCohomologyMapOfHom X α f n
        (moduleResolutionSectionsCohomologyLinearEquiv X α I n x) := by
  let K := moduleResolutionSectionComplex X α I
  let L := moduleResolutionSectionComplex X α J
  let a := ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map φ.hom'
  change moduleResolutionSectionsCohomologyLinearEquiv X α J n
      (HomologicalComplex.homologyMap a (n : ℤ) x) =
    moduleCohomologyMapOfHom X α f n (moduleResolutionSectionsCohomologyLinearEquiv X α I n x)
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance) x
  have hπ := congrArg (fun k => k c) (HomologicalComplex.homologyπ_naturality a (n : ℤ))
  change HomologicalComplex.homologyMap a (n : ℤ) (K.homologyπ n c) =
    L.homologyπ n (HomologicalComplex.cyclesMap a (n : ℤ) c) at hπ
  rw [hπ, moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α J n,
    moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α I n,
    moduleResolutionSectionClass_naturality X α I J φ n]
  apply congrArg (moduleResolutionSectionClass X α J n)
  apply Subtype.ext
  rw [moduleResolutionSectionCyclesIso_hom_val, moduleResolutionSectionCyclesMap_apply,
    moduleResolutionSectionCyclesIso_hom_val]
  exact congrArg (fun k => k c) (HomologicalComplex.cyclesMap_i a (n : ℤ))

end AlgebraicGeometry.Scheme.Cohomology
