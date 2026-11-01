/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PrincipalLocalizationZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingAcyclic
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparison
public import Aglib.CategoryTheory.Limits.CoconeValues
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Acyclicity of original injective coefficients after localization

Every principal stage is an actual open of the original scheme. Exact module
extension by zero makes its module restriction injective, and the original
underlying abelian coefficient is acyclic without being asserted injective.
Actual cohomology-class descent along the principal diagram then proves
acyclicity after an arbitrary multiplicative-set localization of the base.

In particular, localization at a generic point supplies a genuine zero theorem,
not a premise that a given generic class is zero. This concerns localization
of the original injective coefficient on its original source; it does not
assert acyclicity after an arbitrary smooth pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

open Coefficients Stalk ConstantFinite.PrincipalLocalization

universe u e

attribute [local instance] hasSheafifyLarge

/-- The original underlying coefficient of a genuine injective module has
zero positive cohomology, using the actual terminal free-representable source. -/
theorem moduleInjective_cohomology_subsingleton
    (X : Scheme.{u}) [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I]
    (q : ℕ) :
    Subsingleton (Sheaf.H.{e}
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I) (q + 1)) := by
  let F := (SheafOfModules.toSheaf (constantRing X Λ)).obj I
  let E := Sheaf.Hypercohomology.constantIntegerFreeTerminalIso.{u + 1, u, u + 1}
    X.smallEtaleTopology (etaleTerminalIsTerminal X)
  let : Subsingleton (Ext.{e}
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
        X.smallEtaleTopology (etaleTerminal X)) F (q + 1)) :=
    moduleInjective_representedExt_subsingleton X Λ I (etaleTerminal X) q
  exact (Ext.precompIsoAddEquiv E.symm F (q + 1)).injective.subsingleton

/-- Genuine étale restriction, followed by the original scalar-forgetting
comparison, preserves positive acyclicity of an injective module coefficient. -/
theorem moduleInjective_etale_cohomology_subsingleton
    {X U : Scheme.{u}} (j : U ⟶ X) [Etale j]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} U)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I]
    (q : ℕ) :
    Subsingleton (Sheaf.H.{e} ((inverseImage j).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) (q + 1)) := by
  let : Injective ((moduleInverseImage j Λ).obj I) :=
    (moduleLowerShriekAdjunction j Λ).map_injective I inferInstance
  have hzero : Subsingleton (Sheaf.H.{e}
      ((SheafOfModules.toSheaf (constantRing U Λ)).obj
        ((moduleInverseImage j Λ).obj I)) (q + 1)) :=
    moduleInjective_cohomology_subsingleton U Λ ((moduleInverseImage j Λ).obj I) q
  let E : ((SheafOfModules.toSheaf (constantRing U Λ)).obj
      ((moduleInverseImage j Λ).obj I)) ≅
      ((inverseImage j).obj ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) :=
    (moduleInverseImageUnderlyingIso Λ j).app I
  have hinj := (cohomologyMapIso_bijective E.symm (q + 1)).injective
  exact ⟨fun a b => hinj (hzero.elim _ _)⟩

section Localization

variable {R : Type u} [CommRing R] (M : Submonoid R)
  (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
  [CompactSpace X] [QuasiSeparatedSpace X]
  [hExt : ∀ s : Finset M, HasExt.{e} (AbelianSheaf.{u, u + 1}
    ((PrincipalNeighborhoodLimit.baseChangeDiagram M p).obj (op s)))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap R S)))]
  [HasColimitsOfShape (Finset M) AddCommGrpCat.{e}] [UnivLE.{u, e}]

local instance : IsConnected (Finset M) := IsFiltered.isConnected _

local instance (s : Finset M) : CompactSpace ((coefficientDiagram M p).obj s).unop :=
  baseChange_stage_compact M p (op s)

local instance (s : Finset M) :
    QuasiSeparatedSpace ((coefficientDiagram M p).obj s).unop :=
  baseChange_stage_quasiSeparated M p (op s)

local instance (s : Finset M) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((coefficientDiagram M p).obj s).unop) := hExt s

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (coefficientLimitCocone M S p).pt.unop) :=
  inferInstanceAs (HasExt.{e}
    (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap R S))))

local instance {s t : Finset M} (a : s ⟶ t) :
    IsAffineHom ((coefficientDiagram M p).map a).unop :=
  baseChange_transition_affine M p a.op

include M hExt in
/-- Localization of the original qcqs source retains positive acyclicity of
the original injective module coefficient. No generic-zero premise, torsion
condition, Noetherian hypothesis or smooth comparison is used. -/
theorem principalLocalization_moduleInjective_cohomology_subsingleton
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I]
    (q : ℕ) :
    Subsingleton (Sheaf.H.{e}
      ((inverseImage (pullback.fst p (Spec.algebraMap R S))).obj
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) (q + 1)) := by
  let D := coefficientDiagram M p
  let b := coefficientBaseCone M p
  let c := coefficientLimitCocone M S p
  let l : b.pt ⟶ c.pt := (pullback.fst p (Spec.algebraMap R S)).op
  have hc : IsColimit c :=
    (baseChangeConeIsLimit M S p).op.whiskerEquivalence (opOpEquivalence (Finset M)).symm
  have hl : ∀ s, b.π.app s ≫ c.ι.app s = l := fun s =>
    congrArg Quiver.Hom.op (baseChangeProjection_base M S p (op s))
  let F := (SheafOfModules.toSheaf (constantRing X Λ)).obj I
  let C := pullbackLimitCohomologyCocone D b c l hl F (q + 1)
  have hC : IsColimit C :=
    isColimitPullbackCohomologyCocone D b c hc l hl F (q + 1)
  have hstage : ∀ s, IsZero
      ((diagramCohomologyFunctor D (pullbackCoefficientSystem D b F) (q + 1)).obj s) := by
    intro s
    let : HasExt.{e} (AbelianSheaf.{u, u + 1}
        ((schemeDiagram M p).obj (op s)).left) := hExt s
    let j := ((schemeDiagram M p).obj (op s)).hom
    let : IsOpenImmersion j := by
      change IsOpenImmersion (pullback.snd (Spec.algebraMap R (stage M s)) p)
      infer_instance
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    exact moduleInjective_etale_cohomology_subsingleton j Λ I q
  have hlim : IsZero C.pt :=
    CoconeValues.isZero_obj_of_preservesColimit (𝟭 AddCommGrpCat.{e}) hC hstage
  exact AddCommGrpCat.subsingleton_of_isZero hlim

end Localization

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
