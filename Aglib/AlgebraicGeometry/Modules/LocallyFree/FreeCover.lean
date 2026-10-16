/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
# Actual local bases from free presentations on an open cover

The cover, generator index types and free-presentation isomorphisms determine
an actual local generating family. Finite index sets give finite local freeness;
the fixed index `ULift (Fin n)` gives the existing `SheafHasRank` predicate.
The final comparison transports a free presentation through a scheme isomorphism.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/FiniteFlatLocallyFree.lean` at frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `d3dc4d7ca161eb1493165b50730ef4e573da5882fd475b4d4d520c066d42a7fb`.
Only the general cover/free-isomorphism prerequisites are included; no finite
morphism or degree construction is imported.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} {I : Type u} {M : X.Modules}

/-- Transport a displayed free restriction to the equivalent over-site module sheaf. -/
def freeIsoOverOfRestrictFreeIso (U : X.Opens)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅ M.restrict U.ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U := by
  let F := (Scheme.Modules.overEquiv U).functor
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  exact (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((SheafOfModules.mapFreeIso F I η).symm ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app M).symm)

/-- The local generators induced by the given free isomorphisms on an open cover. -/
def localGeneratorsOfCoverFreeIso {κ : Type u}
    (U : κ → X.Opens) (hcov : IsOpenCover U) (I : κ → Type u)
    (e : ∀ i, SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (I i) ≅
      M.restrict (U i).ι) : M.LocalGeneratorsData.{u} where
  I := κ
  X := U
  coversTop := by rwa [_root_.Opens.coversTop_iff]
  generators i := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over (U i))
    (I i)).ofEpi (freeIsoOverOfRestrictFreeIso (U i) (e i)).hom

instance localGeneratorsOfCoverFreeIso_isLocallyFree {κ : Type u}
    (U : κ → X.Opens) (hcov : IsOpenCover U) (I : κ → Type u)
    (e : ∀ i, SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (I i) ≅
      M.restrict (U i).ι) :
    (localGeneratorsOfCoverFreeIso U hcov I e).IsLocallyFreeData where
  isIso i := by
    change κ at i
    change IsIso ((SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U i)) (I i)).ofEpi
        (freeIsoOverOfRestrictFreeIso (U i) (e i)).hom).π
    erw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π, Category.id_comp]
    infer_instance

theorem sheafFiniteLocallyFree_of_coverFreeIso {κ : Type u}
    (U : κ → X.Opens) (hcov : IsOpenCover U) (I : κ → Type u)
    [∀ i, Finite (I i)]
    (e : ∀ i, SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (I i) ≅
      M.restrict (U i).ι) : IsFiniteLocallyFree _ M := by
  apply (isFiniteLocallyFree_iff_exists_localBasis M).mpr
  refine ⟨localGeneratorsOfCoverFreeIso U hcov I e, inferInstance, ?_⟩
  exact fun i ↦ inferInstanceAs (Finite (I i))

theorem sheafHasRank_of_coverFreeIso {κ : Type u} {n : ℕ}
    (U : κ → X.Opens) (hcov : IsOpenCover U)
    (e : ∀ i, SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ≅
      M.restrict (U i).ι) : SheafHasRank M n := by
  refine ⟨localGeneratorsOfCoverFreeIso U hcov (fun _ ↦ ULift.{u} (Fin n)) e,
    inferInstance, ?_⟩
  exact fun _ ↦ ⟨Equiv.ulift⟩

/-- Transport a displayed free restriction through an isomorphism of schemes. -/
def freeIsoOfRestrictIso {Y : Scheme.{u}} (e : X ≅ Y) (N : Y.Modules)
    (a : SheafOfModules.free (R := X.ringCatSheaf) I ≅ N.restrict e.hom) :
    SheafOfModules.free (R := Y.ringCatSheaf) I ≅ N := by
  letI : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor e.inv) := inferInstance
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor e.inv) I
    (Scheme.Modules.restrictUnitIso e.inv).symm) ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso a ≪≫
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm.app N) ≪≫
    ((Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app N) ≪≫
    ((Scheme.Modules.restrictFunctorId (X := Y)).app N)

end AlgebraicGeometry.Scheme.Modules
