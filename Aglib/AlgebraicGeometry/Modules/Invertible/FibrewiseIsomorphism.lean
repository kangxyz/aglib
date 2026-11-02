/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Isomorphisms of line bundles detected at geometric points

The criterion uses the native module sheaves and their actual pullback maps.
First, a global scalar whose geometric pullbacks act invertibly is a unit:
its residue at each point is nonzero, and units are detected on stalks.
Local unit trivializations reduce a line-bundle map to this scalar case.
The restriction and stalk comparisons then recover the original map.

This is a proof of the rank-one alternative needed by the relative positive-section
application. It does not supply the larger all-rank finite-locally-free theorem-family
interface in `Aglib.AlgebraicGeometry.Modules.LocallyFree.FibreCriterion`.
The original and test schemes are arbitrary; no reducedness or Noetherian condition is used.

Proof basis: native Aglib `3a4d549981ced306d89d3ed55418c9e6a25f86c4`, with its pinned
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. This proof was developed for the
rank-one gap identified by the R5 `f8a3314ddecffcada2ec721d26d56a937bed9690` migration;
it is not attributed to the incoming predicate definition.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u

private theorem globalScalar_isUnit_of_geometricPullback_isIso {X : Scheme.{u}} (a : Γ(X, ⊤))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ X),
      IsIso ((Scheme.Modules.pullback t).map
        (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a))) : IsUnit a := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
  intro x hx
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro ha
  let K := AlgebraicClosure (X.residueField x)
  let Y := Spec (CommRingCat.of K)
  let t : Y ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
    X.fromSpecResidueField x
  have htpoint : t (IsLocalRing.closedPoint K) = x := by
    change X.fromSpecResidueField x _ = x
    exact Scheme.fromSpecResidueField_apply x _
  let : Field Γ(Y, ⊤) := (isField_of_isIntegral_of_subsingleton Y).toField
  have hzero : t.appTop a = 0 := by
    apply (Y.Γevaluation (IsLocalRing.closedPoint K)).hom.injective
    rw [map_zero]
    have hn := Scheme.Γevaluation_naturality_apply t (IsLocalRing.closedPoint K) a
    have ha' : X.Γevaluation x a = 0 := ha
    have hz : X.Γevaluation (t (IsLocalRing.closedPoint K)) a = 0 :=
      (congrArg (fun y : X ↦ X.Γevaluation y a = 0) htpoint).mpr ha'
    rw [hz, map_zero] at hn
    exact hn.symm
  let φ := globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a
  have : IsIso ((Scheme.Modules.pullback t).map φ) := h K t
  have hz : (Scheme.Modules.pullback t).map φ = 0 := by
    dsimp only [φ]
    rw [pullback_map_globalScalarEndomorphism, hzero]
    have hc : globalScalarCenter Y 0 = 0 := map_zero _
    exact congrArg (fun z : CatCenter Y.Modules ↦
      z.app ((Scheme.Modules.pullback t).obj (SheafOfModules.unit X.ringCatSheaf))) hc
  have hid : (𝟙 ((Scheme.Modules.pullback t).obj
      (SheafOfModules.unit X.ringCatSheaf))) = 0 := by
    apply (cancel_mono ((Scheme.Modules.pullback t).map φ)).mp
    simp [hz]
  let e := pullbackUnitIso t
  have hunit : (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) = 0 := by
    calc
      _ = e.inv ≫ 𝟙 _ ≫ e.hom := by simp
      _ = 0 := by rw [hid]; simp
  have hh := congrArg (fun ψ : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf ↦ ψ.val.app (op ⊤) (1 : Γ(Y, ⊤))) hunit
  exact one_ne_zero (show (1 : Γ(Y, ⊤)) = 0 from hh)


private theorem unitMap_isIso_of_geometricPullback_isIso {X : Scheme.{u}}
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ X),
      IsIso ((Scheme.Modules.pullback t).map φ)) : IsIso φ := by
  let a : Γ(X, ⊤) := φ.val.app (op ⊤) (1 : Γ(X, ⊤))
  have he : φ = globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a := by
    rw [globalScalarEndomorphism_unit]
    apply (unitHomGlobalSectionsEquiv X (SheafOfModules.unit X.ringCatSheaf)).injective
    simp [a, unitHomGlobalSectionsEquiv_apply, unitMul_app]
    rfl
  have ha : IsUnit a := globalScalar_isUnit_of_geometricPullback_isIso a (by
    intro K _ _ t
    rw [← he]
    exact h K t)
  obtain ⟨v, hv⟩ := ha
  rw [he, ← hv]
  exact inferInstanceAs (IsIso (globalScalarIso (SheafOfModules.unit X.ringCatSheaf) v).hom)


open AlgebraicGeometry.Scheme.Modules.Invertible

/-- A map of actual line bundles is an isomorphism if its actual pullback is an isomorphism
at every algebraically closed field-valued point. The scheme may be empty, nonreduced or
non-Noetherian. No cohomology, flatness or finite-presentation theorem-family input is used. -/
theorem lineBundleMap_isIso_of_geometricPullback_isIso {X : Scheme.{u}}
    (L M : LineBundle X) (φ : (show X.Modules from L.val) ⟶ M.val)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ X),
      IsIso ((Scheme.Modules.pullback t).map φ)) : IsIso φ := by
  apply (moduleSheaf_isIso_iff_stalks φ).mpr
  intro x
  obtain ⟨U, hxU, ⟨eL⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
  let xU : U.toScheme := ⟨x, hxU⟩
  let MU := pullbackLineBundle U.ι M
  obtain ⟨V, hxV, ⟨eM⟩⟩ := (isLocallyRankOne_iff_restrict_unit MU.val).mp MU.property xU
  let j : V.toScheme ⟶ X := V.ι ≫ U.ι
  let y : V.toScheme := ⟨xU, hxV⟩
  let eLU : (Scheme.Modules.pullback U.ι).obj L.val ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.val).symm ≪≫ eL
  let eLV : (Scheme.Modules.pullback j).obj L.val ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.pullbackComp V.ι U.ι).symm.app L.val ≪≫
      (Scheme.Modules.pullback V.ι).mapIso eLU ≪≫ pullbackUnitIso V.ι
  let eMV : (Scheme.Modules.pullback j).obj M.val ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.pullbackComp V.ι U.ι).symm.app M.val ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app MU.val).symm ≪≫ eM
  let ψ : SheafOfModules.unit V.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    eLV.inv ≫ (Scheme.Modules.pullback j).map φ ≫ eMV.hom
  have hψ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ V.toScheme),
      IsIso ((Scheme.Modules.pullback t).map ψ) := by
    intro K _ _ t
    have : IsIso ((Scheme.Modules.pullback t).map ((Scheme.Modules.pullback j).map φ)) :=
      (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp t j) φ).mpr (h K (t ≫ j))
    dsimp only [ψ]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have : IsIso ψ := unitMap_isIso_of_geometricPullback_isIso ψ hψ
  have : IsIso ((Scheme.Modules.pullback j).map φ ≫ eMV.hom) :=
    IsIso.of_isIso_comp_left eLV.inv _
  have : IsIso ((Scheme.Modules.pullback j).map φ) :=
    IsIso.of_isIso_comp_right _ eMV.hom
  have : IsIso ((Scheme.Modules.restrictFunctor j).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j) φ).mpr inferInstance
  have hstalk : IsIso ((Scheme.Modules.stalkFunctor V.toScheme y).map
      ((Scheme.Modules.restrictFunctor j).map φ)) :=
    (Scheme.Modules.stalkFunctor V.toScheme y).map_isIso
      ((Scheme.Modules.restrictFunctor j).map φ)
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso j y) φ).mp hstalk

end AlgebraicGeometry.Scheme.Modules.Invertible
