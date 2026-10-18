/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Truncation
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Derived

/-! # The finite Cech model and installed derived global sections

The original bounded good Cech truncation maps by its literal inclusion to the
original integer Cech complex. The native `QCompιIso.inv` then compares full
localization with the bounded-below inclusion, and the original Cech derived
comparison identifies this with installed right-derived global sections.

Every coefficient map and every actual injective-resolution lift preserves
these exact forward factors. The comparison is independent of the supplied
resolution. The existing quasicoherence, separatedness and finite affine-cover
hypotheses suffice; no flatness or Noetherian hypothesis is introduced.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {ι : Type u} (U : ι → X.Opens) [X.IsSeparated]
  (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M)
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

/-- The standard derived-category model for modules on `X`, used locally. -/
local instance finiteCechDerivedSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance finiteCechDerivedTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

include hU in
private theorem finiteCechTuple_isAffine (q : ℕ) (a : Fin (q + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => U (a k)) := by
  have h : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
    apply le_antisymm
    · exact le_iInf fun k => leOfHom (Pi.π _ k)
    · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
  rw [h]
  exact IsAffineOpen.iInf (fun k => hU (a k))

include e hU hcover

/-- The actual finite Cech model represents installed derived global sections in the full category.
-/
def moduleFiniteCechDerivedGlobalSectionsIso :
    DerivedCategory.Q.obj (moduleFiniteCechComplex X α U M n) ≅
      DerivedCategory.Plus.ι.obj
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  letI := moduleFiniteCechInclusion_quasiIso X α U M n e hU hcover
  letI : IsIso (DerivedCategory.Q.map (moduleFiniteCechInclusion X α U M n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mpr inferInstance
  exact asIso (DerivedCategory.Q.map (moduleFiniteCechInclusion X α U M n)) ≪≫
    (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).symm.app
      (moduleCechComplexPlus X α U M) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (moduleCechDerivedGlobalSectionsIso X α U I hcover (by
        intro q a
        exact finiteCechTuple_isAffine X U hU q a))

/-- The forward map retains the original inclusion, native full inclusion, and original Cech model.
-/
@[reassoc]
theorem moduleFiniteCechDerivedGlobalSectionsIso_hom :
    letI := moduleFiniteCechInclusion_quasiIso X α U M n e hU hcover
    (moduleFiniteCechDerivedGlobalSectionsIso X α U M I n e hU hcover).hom =
      DerivedCategory.Q.map (moduleFiniteCechInclusion X α U M n) ≫
        (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).inv.app
          (moduleCechComplexPlus X α U M) ≫
        DerivedCategory.Plus.ι.map
          (moduleCechDerivedGlobalSectionsIso X α U I hcover (by
            intro q a
            exact finiteCechTuple_isAffine X U hU q a)).hom := rfl

section Naturality
variable {N : X.Modules} [N.IsQuasicoherent] {J : InjectiveResolution N} {f : M ⟶ N}

/-- Every original coefficient map and supplied resolution lift preserves the actual finite model.
-/
@[reassoc]
theorem moduleFiniteCechDerivedGlobalSectionsIso_naturality
    (φ : InjectiveResolution.Hom I J f) :
    DerivedCategory.Q.map ((moduleFiniteCechFunctor X α U n).map f) ≫
      (moduleFiniteCechDerivedGlobalSectionsIso X α U N J n e hU hcover).hom =
    (moduleFiniteCechDerivedGlobalSectionsIso X α U M I n e hU hcover).hom ≫
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) := by
  let haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)) :=
    finiteCechTuple_isAffine X U hU
  let iM := moduleFiniteCechInclusion X α U M n
  let iN := moduleFiniteCechInclusion X α U N n
  have hι := congrArg (fun g => DerivedCategory.Q.map g)
    (moduleFiniteCechInclusion_naturality X α U f n)
  have hQ := (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).inv.naturality
    (moduleCechComplexPlusMap X α (U := U) f)
  change DerivedCategory.Q.map ((moduleCechIntFunctor X α U).map f) ≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).inv.app
        (moduleCechComplexPlus X α U N) =
    (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).inv.app
      (moduleCechComplexPlus X α U M) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
        (moduleCechComplexPlusMap X α (U := U) f)) at hQ
  have hC := congrArg (fun g => DerivedCategory.Plus.ι.map g)
    (moduleCechDerivedGlobalSectionsIso_naturality X α U hcover haff φ)
  simp only [CategoryTheory.Functor.map_comp] at hι hC
  rw [moduleFiniteCechDerivedGlobalSectionsIso_hom,
    moduleFiniteCechDerivedGlobalSectionsIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hι, reassoc_of% hQ, hC]

end Naturality



/-- The native finite-model comparison is independent of the supplied injective resolution. -/
theorem moduleFiniteCechDerivedGlobalSectionsIso_eq (J : InjectiveResolution M) :
    moduleFiniteCechDerivedGlobalSectionsIso X α U M I n e hU hcover =
      moduleFiniteCechDerivedGlobalSectionsIso X α U M J n e hU hcover := by
  let φ : InjectiveResolution.Hom I J (𝟙 M) := {
    hom := InjectiveResolution.desc (𝟙 M) J I
    ι_f_zero_comp_hom_f_zero := by
      simpa only [HomologicalComplex.comp_f] using
        HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes (𝟙 M) J I) 0 }
  apply Iso.ext
  have h := moduleFiniteCechDerivedGlobalSectionsIso_naturality X α U M I n e hU hcover φ
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

end AlgebraicGeometry.Scheme.Cohomology
