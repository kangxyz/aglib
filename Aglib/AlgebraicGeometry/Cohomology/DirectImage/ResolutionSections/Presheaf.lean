/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open.Naturality
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Functor

/-!
# Native resolution-presheaf homology and original open cohomology

The source is literally native homology of the original module-valued
section-presheaf complex of the supplied actual module injective resolution.
Evaluation and its native homology comparison identify its values with the
original open-section homology. The resulting presheaf isomorphism has the
unchanged native `Sheaf.H'` presheaf as target, with its original actions and
restriction maps. Only the small native source is lifted in universe.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {M : X.Modules} (I : InjectiveResolution M)

/-- The original native section-presheaf functor applied to the actual module resolution. -/
abbrev moduleResolutionSectionsPresheafComplex :
    CochainComplex (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) ℤ :=
  ((moduleSectionsPresheafFunctor X α).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

/-- Native evaluation of presheaf homology is actual open-section homology. -/
def moduleResolutionSectionsPresheafHomologyEvaluationIso (U : X.Opens) (n : ℕ) :
    ((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).obj (op U) ≅
      (moduleResolutionOpenSectionComplex X α U I).homology (n : ℤ) :=
  (((moduleResolutionSectionsPresheafComplex X α I).sc (n : ℤ)).mapHomologyIso
    ((CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U))).symm

/-- The native evaluation comparison retains the actual restriction of the supplied resolution. -/
theorem moduleResolutionSectionsPresheafHomologyEvaluationIso_naturality
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    ((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).map i ≫
        (moduleResolutionSectionsPresheafHomologyEvaluationIso X α I V.unop n).hom =
      (moduleResolutionSectionsPresheafHomologyEvaluationIso X α I U.unop n).hom ≫
        HomologicalComplex.homologyMap (moduleResolutionOpenSectionRestriction X α i.unop I)
          (n : ℤ) := by
  let K := moduleResolutionSectionsPresheafComplex X α I
  let τ := (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).map i
  have h := τ.app_homology (K.sc (n : ℤ))
  change (K.homology (n : ℤ)).map i =
      (moduleResolutionSectionsPresheafHomologyEvaluationIso X α I U.unop n).hom ≫
        HomologicalComplex.homologyMap (moduleResolutionOpenSectionRestriction X α i.unop I)
          (n : ℤ) ≫
        (moduleResolutionSectionsPresheafHomologyEvaluationIso X α I V.unop n).inv at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Actual native homology of the actual resolution section presheaf is the original native
open-cohomology presheaf. The original target is not shrunk or redefined. -/
def moduleResolutionSectionsHomologyPresheafIso (n : ℕ) :
    (moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ) ⋙
        ModuleCat.uliftFunctor.{u + 1, u} R ≅ moduleHPrimePresheaf X α M n := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · letI := moduleHPrimeModuleOfHom X α M n V.unop
    exact ((ULift.moduleEquiv :
        ULift.{u + 1, u}
            (((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).obj V) ≃ₗ[R]
          ((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).obj V).trans
      ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α I V.unop n).toLinearEquiv.trans
        (moduleResolutionOpenSectionsCohomologyLinearEquiv X α V.unop I n))).toModuleIso
  · intro V W i
    ext x
    change moduleResolutionOpenSectionsCohomologyLinearEquiv X α W.unop I n
        ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α I W.unop n).hom
          (((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).map i x.down)) =
      moduleHPrimeRestrictionOfHom X α M n i.unop
        (moduleResolutionOpenSectionsCohomologyLinearEquiv X α V.unop I n
          ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α I V.unop n).hom x.down))
    have h := ConcreteCategory.congr_hom
      (moduleResolutionSectionsPresheafHomologyEvaluationIso_naturality X α I i n) x.down
    change (moduleResolutionSectionsPresheafHomologyEvaluationIso X α I W.unop n).hom
        (((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).map i x.down) =
      HomologicalComplex.homologyMap (moduleResolutionOpenSectionRestriction X α i.unop I)
        (n : ℤ)
        ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α I V.unop n).hom x.down) at h
    rw [h]
    exact moduleResolutionOpenSectionsCohomologyLinearEquiv_restriction X α i.unop I n _

/-- The original presheaf comparison has its actual section-homology forward map. -/
theorem moduleResolutionSectionsHomologyPresheafIso_hom_app_apply (n : ℕ) (U : X.Opensᵒᵖ)
    (x : ((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ) ⋙
      ModuleCat.uliftFunctor.{u + 1, u} R).obj U) :
    (moduleResolutionSectionsHomologyPresheafIso X α I n).hom.app U x =
      moduleResolutionOpenSectionsCohomologyLinearEquiv X α U.unop I n
        ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α I U.unop n).hom x.down) := rfl

/-- The original presheaf comparison retains every actual module coefficient-resolution lift. -/
theorem moduleResolutionSectionsHomologyPresheafIso_coefficient_naturality
    {N : X.Modules} (J : InjectiveResolution N) {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) (U : X.Opensᵒᵖ)
    (x : ((moduleResolutionSectionsPresheafComplex X α I).homology (n : ℤ)).obj U) :
    (moduleResolutionSectionsHomologyPresheafIso X α J n).hom.app U
        (ULift.up ((HomologicalComplex.homologyMap
          (((moduleSectionsPresheafFunctor X α).mapHomologicalComplex (.up ℤ)).map φ.hom')
            (n : ℤ)).app U x)) =
      moduleHPrimeMapOfHom X α f n U.unop
        ((moduleResolutionSectionsHomologyPresheafIso X α I n).hom.app U (ULift.up x)) := by
  let a := ((moduleSectionsPresheafFunctor X α).mapHomologicalComplex (.up ℤ)).map φ.hom'
  let E := (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj U
  have he := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ) (n : ℤ)).map a) E
  have h := ConcreteCategory.congr_hom he x
  change (moduleResolutionSectionsPresheafHomologyEvaluationIso X α J U.unop n).hom
      ((HomologicalComplex.homologyMap a (n : ℤ)).app U x) =
    HomologicalComplex.homologyMap
      (((moduleOpenSectionsFunctorOfHom X α U.unop).mapHomologicalComplex (.up ℤ)).map φ.hom')
        (n : ℤ)
        ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α I U.unop n).hom x) at h
  rw [moduleResolutionSectionsHomologyPresheafIso_hom_app_apply,
    moduleResolutionSectionsHomologyPresheafIso_hom_app_apply]
  change moduleResolutionOpenSectionsCohomologyLinearEquiv X α U.unop J n
      ((moduleResolutionSectionsPresheafHomologyEvaluationIso X α J U.unop n).hom
        ((HomologicalComplex.homologyMap a (n : ℤ)).app U x)) = _
  rw [h]
  exact moduleResolutionOpenSectionsCohomologyLinearEquiv_naturality X α U.unop I J φ n _

end AlgebraicGeometry.Scheme.Cohomology
