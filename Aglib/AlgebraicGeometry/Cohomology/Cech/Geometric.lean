/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.DegreeZero
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor

/-!
# Geometric naturality of the original Cech computation

For arbitrary schemes, module coefficients and an actual coefficient map along
geometric inverse image, the Cech comparison commutes with the original
Ext-defined `zariskiCohomologyMap`. The two total augmentations and the exact
inverse-image lift identify the map on actual resolution cycles and homology.

The cover, affine-intersection and quasicoherence hypotheses remain explicit.
There is no field, finiteness or supplied comparison hypothesis. These generic
proofs are extracted from the field-base-change owner for reuse with general
coefficient rings; their mathematical declaration names remain unchanged.
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

section GeometricHomology
open HomologicalComplex₂ HomologicalComplex₂.AddCommGrp
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
variable (M : Y.Modules) [M.IsQuasicoherent] (N : X.Modules) [N.IsQuasicoherent]
variable (R : InjectiveResolution (moduleAddSheaf Y M))
variable (S : InjectiveResolution (moduleAddSheaf X N))
variable (hcover : iSup U = ⊤)
variable (hcover' : (⨆ i, f ⁻¹ᵁ U i) = ⊤)
variable (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
variable (haff' : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => f ⁻¹ᵁ U (a k)))
variable (a : (zariskiPullback f).obj (moduleAddSheaf Y M) ⟶ moduleAddSheaf X N)
variable (φ : ((zariskiPullback f).mapHomologicalComplex _).obj R.cocomplex ⟶ S.cocomplex)
variable (hφ : (zariskiPullback f).map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0)

include hφ

/-- The two genuine total augmentations intertwine the actual geometric Cech map with the
  adjoint section-complex map. -/
theorem moduleCechResolutionHomologyIso_geometric (n : ℕ) :
    homologyMap (additiveCechGeometricMap f U _ _ a) n ≫
      (moduleCechResolutionHomologyIso (fun i => f ⁻¹ᵁ U i) N S hcover' haff' n).hom =
    (moduleCechResolutionHomologyIso U M R hcover haff n).hom ≫
      homologyMap (geometricResolutionSectionsMap f φ) n := by
  have := additiveResolutionSectionsToTotal_quasiIso (fun i => f ⁻¹ᵁ U i) S hcover'
  apply (cancel_mono (homologyMap (additiveResolutionSectionsToTotal (fun i => f ⁻¹ᵁ U i) S) n)).mp
  have hc := congrArg (fun g => homologyMap g n)
    (totalAugmentation_naturality (additiveCechColumnAugmentation U R)
      (additiveCechColumnAugmentation (fun i => f ⁻¹ᵁ U i) S)
      (additiveCechGeometricMap f U _ _ a) (geometricCechResolutionMap f U R S φ)
      (geometricCechColumnAugmentation_naturality f U R S φ a hφ))
  have hr := congrArg (fun g => homologyMap g n)
    (totalAugmentationFlip_naturality (additiveCechRowAugmentation U R)
      (additiveCechRowAugmentation (fun i => f ⁻¹ᵁ U i) S)
      (geometricResolutionSectionsMap f φ) (geometricCechResolutionMap f U R S φ)
      (geometricCechRowAugmentation_naturality f U R S φ))
  simp only [homologyMap_comp] at hc hr
  change homologyMap (additiveCechGeometricMap f U _ _ a) n ≫
      homologyMap (additiveCechToTotal (fun i => f ⁻¹ᵁ U i) S) n =
    homologyMap (additiveCechToTotal U R) n ≫
      homologyMap (HomologicalComplex₂.total.map (geometricCechResolutionMap f U R S φ) (.up ℕ)) n
      at hc
  change homologyMap (geometricResolutionSectionsMap f φ) n ≫
      homologyMap (additiveResolutionSectionsToTotal (fun i => f ⁻¹ᵁ U i) S) n =
    homologyMap (additiveResolutionSectionsToTotal U R) n ≫
      homologyMap (HomologicalComplex₂.total.map (geometricCechResolutionMap f U R S φ) (.up ℕ)) n
      at hr
  rw [Category.assoc, moduleCechResolutionHomologyIso_hom_comp,
    Category.assoc, hr, ← Category.assoc, moduleCechResolutionHomologyIso_hom_comp]
  exact hc

end GeometricHomology

section OriginalGeometricExt
open HomologicalComplex CategoryTheory.InjectiveResolution.ExactFunctor
section GeometricResolution
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
  {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
variable (R : InjectiveResolution A) (S : InjectiveResolution B)
variable (a : (zariskiPullback f).obj A ⟶ B)
variable (φ : ((zariskiPullback f).mapHomologicalComplex _).obj R.cocomplex ⟶ S.cocomplex)
variable (hφ : (zariskiPullback f).map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0)

/-- The actual map on global resolution cycles induced by a geometric lift. -/
def geometricResolutionCyclesMap (n : ℕ) :
    resolutionSectionCycles R n →+ resolutionSectionCycles S n where
  toFun s := ⟨(geometricResolutionSectionsMap f φ).f n s.val, by
    have h := ConcreteCategory.congr_hom ((geometricResolutionSectionsMap f φ).comm n (n + 1)) s.val
    change resolutionSectionDifferential S n (n + 1)
      ((geometricResolutionSectionsMap f φ).f n s.val) =
        (geometricResolutionSectionsMap f φ).f (n + 1)
          (resolutionSectionDifferential R n (n + 1) s.val) at h
    rw [s.property, map_zero] at h
    exact h⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' s t := by apply Subtype.ext; exact map_add _ _ _

include hφ in
/-- The original zariskiCohomologyMap is represented by the genuine adjoint resolution-cycle map. -/
theorem geometricResolutionSectionClass_naturality (n : ℕ) (s : resolutionSectionCycles R n) :
    resolutionSectionClass S n (geometricResolutionCyclesMap f R S φ n s) =
      zariskiCohomologyMap f A B a n (resolutionSectionClass R n s) := by
  let t := (integerSheafHomEquiv (R.cocomplex.X n)).symm s.val
  have ht : t ≫ R.cocomplex.d n (n + 1) = 0 := by
    rw [integerSheafHomEquiv_symm_comp]
    exact (integerSheafHomEquiv _).symm.map_eq_zero_iff.mpr s.property
  have hc := mk₀_comp_extMk_mapExactFunctor_comp_mk₀
    (zariskiPullback f) R S a φ hφ t ht
    ((constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)))
  have hv : (integerSheafHomEquiv (S.cocomplex.X n)).symm
      ((geometricResolutionSectionsMap f φ).f n s.val) ≫ S.cocomplex.d n (n + 1) = 0 := by
    rw [integerSheafHomEquiv_symm_comp]
    exact (integerSheafHomEquiv _).symm.map_eq_zero_iff.mpr
      (geometricResolutionCyclesMap f R S φ n s).property
  change S.extMk ((integerSheafHomEquiv (S.cocomplex.X n)).symm
      ((geometricResolutionSectionsMap f φ).f n s.val)) (n + 1) rfl hv = _
  change _ = ((Abelian.Ext.mk₀ ((constantPullbackIso f).inv.app
      (AddCommGrpCat.of (ULift.{u} ℤ)))).comp
        ((R.extMk t (n + 1) rfl ht).mapExactFunctor (zariskiPullback f))
          (Nat.zero_add n)).comp (Abelian.Ext.mk₀ a) (Nat.add_zero n)
  rw [hc]
  congr 1
  apply (integerSheafHomEquiv (S.cocomplex.X n)).injective
  rw [AddEquiv.apply_symm_apply]
  exact (geometricResolutionSectionsMap_integerHom f R S φ n s.val).symm

/-- The three consecutive global-section groups of an additive injective resolution. -/
abbrev canonicalResolutionShort {Z : Scheme.{u}}
    {C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (Q : InjectiveResolution C) (n : ℕ) :=
  ((((additiveSectionsFunctor Z ⊤).mapHomologicalComplex _).obj Q.cocomplex).sc'
    n (n + 1) (n + 2))

/-- The section short-complex map induced by a chosen geometric resolution lift. -/
abbrev geometricResolutionShortMap (n : ℕ) :
    canonicalResolutionShort R n ⟶ canonicalResolutionShort S n :=
  (shortComplexFunctor' AddCommGrpCat.{u} (.up ℕ) n (n + 1) (n + 2)).map
    (geometricResolutionSectionsMap f φ)

include hφ in
/-- Cycle and quotient maps realizing the actual geometric cohomology map. -/
def geometricResolutionHomologyMapData (n : ℕ) :
    ShortComplex.LeftHomologyMapData (geometricResolutionShortMap f R S φ n)
      (canonicalResolutionShort R n).abLeftHomologyData
      (canonicalResolutionShort S n).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (geometricResolutionCyclesMap f R S φ (n + 1))
  φH := AddCommGrpCat.ofHom
    ((resolutionSectionsCohomologyEquiv S n).symm.toAddMonoidHom.comp
      ((zariskiCohomologyMap f A B a (n + 1)).comp
        (resolutionSectionsCohomologyEquiv R n).toAddMonoidHom))
  commi := by ext s; rfl
  commf' := by
    ext s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((geometricResolutionSectionsMap f φ).comm n (n + 1)).symm s
  commπ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply (resolutionSectionsCohomologyEquiv S n).injective
    change resolutionSectionsCohomologyEquiv S n
      ((resolutionSectionsCohomologyEquiv S n).symm
        (zariskiCohomologyMap f A B a (n + 1) (resolutionSectionsCohomologyEquiv R n
          (QuotientAddGroup.mk' (resolutionSectionBoundary R n).range s)))) =
      resolutionSectionsCohomologyEquiv S n
        (QuotientAddGroup.mk' (resolutionSectionBoundary S n).range
          (geometricResolutionCyclesMap f R S φ (n + 1) s))
    rw [AddEquiv.apply_symm_apply, resolutionSectionsCohomologyEquiv_mk,
      resolutionSectionsCohomologyEquiv_mk]
    exact (geometricResolutionSectionClass_naturality f R S a φ hφ (n + 1) s).symm

/-- Section short-complex homology identified with the original positive `Sheaf.H`. -/
def canonicalResolutionShortEquiv {Z : Scheme.{u}}
    {C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (Q : InjectiveResolution C) (n : ℕ) :
    (canonicalResolutionShort Q n).homology ≃+ Sheaf.H.{u + 1} C (n + 1) :=
  (canonicalResolutionShort Q n).abHomologyIso.addCommGroupIsoToAddEquiv.trans
    (resolutionSectionsCohomologyEquiv Q n)

include hφ in
private theorem geometricResolutionShortEquiv_naturality (n : ℕ)
    (x : (canonicalResolutionShort R n).homology) :
    canonicalResolutionShortEquiv S n
      (ShortComplex.homologyMap (geometricResolutionShortMap f R S φ n) x) =
      zariskiCohomologyMap f A B a (n + 1) (canonicalResolutionShortEquiv R n x) := by
  have h := congrArg (fun q => resolutionSectionsCohomologyEquiv S n (q.hom x))
    (geometricResolutionHomologyMapData f R S a φ hφ n).homologyMap_comm
  change canonicalResolutionShortEquiv S n
    (ShortComplex.homologyMap (geometricResolutionShortMap f R S φ n) x) =
      resolutionSectionsCohomologyEquiv S n ((resolutionSectionsCohomologyEquiv S n).symm
        (zariskiCohomologyMap f A B a (n + 1) (canonicalResolutionShortEquiv R n x))) at h
  simpa only [AddEquiv.apply_symm_apply] using h

include hφ in
/-- The original positive-degree zariskiCohomologyMap is the actual map on global resolution
  homology. -/
theorem additiveResolutionHomologyEquiv_geometric (n : ℕ)
    (x : (((additiveSectionsFunctor Y ⊤).mapHomologicalComplex _).obj R.cocomplex).homology (n +
      1)) :
    additiveResolutionHomologyEquiv S n
      (homologyMap (geometricResolutionSectionsMap f φ) (n + 1) x) =
    zariskiCohomologyMap f A B a (n + 1) (additiveResolutionHomologyEquiv R n x) := by
  let C := ((additiveSectionsFunctor Y ⊤).mapHomologicalComplex _).obj R.cocomplex
  let D := ((additiveSectionsFunctor X ⊤).mapHomologicalComplex _).obj S.cocomplex
  let g := geometricResolutionSectionsMap f φ
  have hsc : homologyMap g (n + 1) ≫
      (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
    (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap (geometricResolutionShortMap f R S φ n) := by
    simpa [homologyFunctorIso', homologyFunctorIso, homologyIsoSc'] using
      (homologyFunctorIso' AddCommGrpCat.{u} (.up ℕ) n (n + 1) (n + 2) (by simp) (by
        simp)).hom.naturality g
  change canonicalResolutionShortEquiv S n
    ((D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
      (homologyMap g (n + 1) x)) =
    zariskiCohomologyMap f A B a (n + 1) (canonicalResolutionShortEquiv R n
      ((C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))
  rw [show (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
      (homologyMap g (n + 1) x) =
    ShortComplex.homologyMap (geometricResolutionShortMap f R S φ n)
      ((C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x) from
        ConcreteCategory.congr_hom hsc x]
  exact geometricResolutionShortEquiv_naturality f R S a φ hφ n _

end GeometricResolution

section GeometricCech
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
variable (M : Y.Modules) [M.IsQuasicoherent] (N : X.Modules) [N.IsQuasicoherent]
variable (R : InjectiveResolution (moduleAddSheaf Y M))
variable (S : InjectiveResolution (moduleAddSheaf X N))
variable (hcover : iSup U = ⊤)
variable (hcover' : (⨆ i, f ⁻¹ᵁ U i) = ⊤)
variable (haff : ∀ (p : ℕ) (b : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (b k)))
variable (haff' : ∀ (p : ℕ) (b : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => f ⁻¹ᵁ U (b k)))
variable (a : (zariskiPullback f).obj (moduleAddSheaf Y M) ⟶ moduleAddSheaf X N)

/-- The genuine Cech comparison is natural for the unchanged zariskiCohomologyMap and every
  compatible lift. -/
theorem moduleCechCohomologyAddEquiv_geometric_of_lift
    (φ : ((zariskiPullback f).mapHomologicalComplex _).obj R.cocomplex ⟶ S.cocomplex)
    (hφ : (zariskiPullback f).map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0)
    (n : ℕ) (x : ((additiveCechFunctor Y U).obj (moduleAddSheaf Y M)).homology (n + 1)) :
    moduleCechCohomologyAddEquiv (fun i => f ⁻¹ᵁ U i) N S hcover' haff' n
      (homologyMap (additiveCechGeometricMap f U _ _ a) (n + 1) x) =
    zariskiCohomologyMap f _ _ a (n + 1) (moduleCechCohomologyAddEquiv U M R hcover haff n x) := by
  have h := ConcreteCategory.congr_hom
    (moduleCechResolutionHomologyIso_geometric f U M N R S hcover hcover' haff haff' a φ hφ (n +
      1)) x
  simp only [ConcreteCategory.comp_apply] at h
  change additiveResolutionHomologyEquiv S n
    ((moduleCechResolutionHomologyIso (fun i => f ⁻¹ᵁ U i) N S hcover' haff' (n + 1)).hom
      (homologyMap (additiveCechGeometricMap f U _ _ a) (n + 1) x)) = _
  rw [h]
  exact additiveResolutionHomologyEquiv_geometric f R S a φ hφ n _

/-- Actual exact inverse image constructs the lift, so the geometric Cech/H square has no
  supplied cohomological comparison premise. -/
theorem moduleCechCohomologyAddEquiv_geometric
    (n : ℕ) (x : ((additiveCechFunctor Y U).obj (moduleAddSheaf Y M)).homology (n + 1)) :
    moduleCechCohomologyAddEquiv (fun i => f ⁻¹ᵁ U i) N S hcover' haff' n
      (homologyMap (additiveCechGeometricMap f U _ _ a) (n + 1) x) =
    zariskiCohomologyMap f _ _ a (n + 1) (moduleCechCohomologyAddEquiv U M R hcover haff n x) :=
  moduleCechCohomologyAddEquiv_geometric_of_lift f U M N R S hcover hcover' haff haff' a
    (lift (zariskiPullback f) R S a) (lift_commutes_zero (zariskiPullback f) R S a) n x

end GeometricCech

end OriginalGeometricExt

end AlgebraicGeometry.Scheme.Cohomology
