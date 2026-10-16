/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite local bases and actual field fibres

An actual finite local basis pulls back through a field-valued point to the
free sheaf on the same index type. Its actual field sections identify with
the corresponding finite product of the field, including an empty index type.
The pointwise theorem `moduleFibre_finite_and_finrank_eq_card` uses the native `moduleFibre`,
its original field scalars, and the same universe as the scheme.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/LocalBasisFibreDimension.lean`
at frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `8a4dad67db90e8e457f18bcce4a99164bb2195449afb711af4e238d60b5717a4`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Global sections on the spectrum of a field, with scalars transported through
`Scheme.ΓSpecIso`, as in the existing `fieldSections` definition. -/
def fieldSectionsFunctor (K : Type u) [Field K] :
    (Spec (CommRingCat.of K)).Modules ⥤ ModuleCat K :=
  SheafOfModules.evaluation _ (op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

instance (K : Type u) [Field K] : PreservesFiniteLimits (fieldSectionsFunctor K) := by
  let F := SheafOfModules.evaluation.{u} (Spec (CommRingCat.of K)).ringCatSheaf (op ⊤)
  let G := ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hG := ((Functor.exact_tfae G).out 2 4).mp
    (ModuleCat.restrictScalars_map_exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  letI : PreservesFiniteLimits G := hG.1
  exact comp_preservesFiniteLimits F G

/-- The field-valued global sections of the structure module are the field. -/
def fieldSectionsUnitEquiv (K : Type u) [Field K] :
    fieldSections K (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf) ≃ₗ[K] K where
  toFun := (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  invFun := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  left_inv := by
    intro x
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id x
  right_inv := by
    intro x
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id x
  map_add' := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.map_add
  map_smul' k x := by
    change Γ(Spec (CommRingCat.of K), ⊤) at x
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k * x) =
        k * (Scheme.ΓSpecIso (CommRingCat.of K)).hom x
    rw [map_mul]
    congr 1
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id k

/-- A finite free sheaf on a field spectrum has the expected vector space of
sections; the index type can be empty. -/
def fieldSectionsFreeEquiv (K : Type u) [Field K] (I : Type u) [Finite I] :
    fieldSections K (SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf) I)
      ≃ₗ[K] (I → K) := by
  letI := Fintype.ofFinite I
  let X := Spec (CommRingCat.of K)
  let f : I → X.Modules := fun _ ↦ SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct f := HasBiproduct.of_hasProduct f
  let e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ ∏ᶜ f :=
    (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f
  let e' : (fieldSectionsFunctor K).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ModuleCat.of K (I → K) :=
    (fieldSectionsFunctor K).mapIso e ≪≫
      PreservesProduct.iso (fieldSectionsFunctor K) f ≪≫
      Pi.mapIso (fun _ ↦ (fieldSectionsUnitEquiv K).toModuleIso) ≪≫
      ModuleCat.piIsoPi (fun _ : I ↦ ModuleCat.of K K)
  exact e'.toLinearEquiv

variable {Y : Scheme.{u}}

/-- The given chart's actual generating isomorphism, transported from the over
site to the open subscheme and then to the usual pullback. -/
def localBasisRestrictedIso (M : Y.Modules) (q : M.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) (i : q.I) :
    SheafOfModules.free (R := (Scheme.Opens.toScheme (X := Y) (q.X i)).ringCatSheaf)
      (q.generators i).I ≅
      (Scheme.Modules.pullback (Scheme.Opens.ι (X := Y) (q.X i))).obj M := by
  letI := hq
  let U : Y.Opens := q.X i
  let E := (Scheme.Modules.overEquiv U).functor
  let eunit : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      E.obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) :=
    (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm
  exact SheafOfModules.mapFreeIso E (q.generators i).I eunit ≪≫
    E.mapIso (asIso (q.generators i).π) ≪≫
    (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M

/-- Pull the actual chart basis through a field-valued point in that chart. -/
def localBasisFibreIsoFree (M : Y.Modules) (q : M.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) (K : Type u) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ Y) (i : q.I) (hi : p default ∈ q.X i) :
    (Scheme.Modules.pullback p).obj M ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf) (q.generators i).I := by
  let U : Y.Opens := q.X i
  have hr : Set.range p ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨p x, ?_⟩, rfl⟩
    simpa only [Subsingleton.elim x default] using hi
  let p' := IsOpenImmersion.lift U.ι p hr
  have hp : p' ≫ U.ι = p := IsOpenImmersion.lift_fac U.ι p hr
  exact (Scheme.Modules.pullbackCongr hp.symm).app M ≪≫
    (Scheme.Modules.pullbackComp p' U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback p').mapIso (localBasisRestrictedIso M q hq i).symm ≪≫
    SheafOfModules.pullbackObjFreeIso p'.toRingCatSheafHom (q.generators i).I

/-- A finite local basis makes the actual field fibre finite, with dimension equal
to the number of generators on any chart containing the point. -/
theorem moduleFibre_finite_and_finrank_eq_card (Y : Scheme.{u}) (M : Y.Modules)
    (q : M.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData)
    (hfin : ∀ i, Finite (q.generators i).I) (K : Type u) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ Y) (i : q.I) (hi : p default ∈ q.X i) :
    Module.Finite K (moduleFibre K M p) ∧
      Module.finrank K (moduleFibre K M p) = Nat.card (q.generators i).I := by
  letI := hfin i
  letI := Fintype.ofFinite (q.generators i).I
  let e : moduleFibre K M p ≃ₗ[K] ((q.generators i).I → K) :=
    (fieldSectionsIso K (localBasisFibreIsoFree M q hq K p i hi)).trans
      (fieldSectionsFreeEquiv K (q.generators i).I)
  exact ⟨Module.Finite.equiv e.symm, by
    rw [e.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]⟩

end AlgebraicGeometry.Scheme.Modules
