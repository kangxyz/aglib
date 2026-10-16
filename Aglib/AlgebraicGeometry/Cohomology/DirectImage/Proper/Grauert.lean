/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Grauert.Global
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Affine
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
# Proper Grauert finite local freeness over an arbitrary reduced locally Noetherian target

Locally constant intrinsic ordinary fibre-cohomology dimension makes the
actual natural-degree higher direct image finite locally free. Each actual
target affine open uses the same original affine proper Grauert theorem.
The original higher-image open comparison and the original affine-sections
cohomology equivalence transfer projectivity to its small actual section
module. Proper coherence supplies finite generation, and the native tilde
counit recovers the actual restricted higher image.

The target need not be quasi-compact, and no uniform global cohomological
bound, flatness of the proper morphism, or theorem family is assumed.
Relative flatness is the intrinsic property of the original coefficient.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

/-- On a reduced locally Noetherian target, locally constant original ordinary
fibre-cohomology dimension makes the actual proper higher direct image finite
locally free. Neither a quasi-compact target nor flatness of the morphism is required. -/
theorem moduleHigherDirectImage_finiteLocallyFree_of_isLocallyConstant_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (modulePointFiberCohomologyDimension f M q)) :
    SheafFiniteLocallyFree (((pushforward f).rightDerived q).obj M) := by
  let H := ((pushforward f).rightDerived q).obj M
  have hH : affineLocallyFiniteType Y H := moduleHigherDirectImage_coherent_of_proper f M hM q
  let U := Y.affineOpenCover
  apply finiteLocallyFree_of_affineCharts H U.X U.f (fun y => ⟨U.idx y, U.covers y⟩)
  intro i
  let A := U.X i
  let j := U.f i
  let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let : AlgebraicGeometry.IsReduced (Spec A) := isReduced_of_isOpenImmersion j
  let : _root_.IsReduced A := (affine_isReduced_iff A).mp inferInstance
  let a := pullback.fst f j
  let b := pullback.snd f j
  let W := CategoryTheory.Limits.pullback f j
  let N := (Scheme.Modules.pullback a).obj M
  let C := (restrictFunctorIsoPullback a).app M
  have hN : affineLocallyFiniteType W N :=
    (affineLocallyFiniteType W).prop_of_iso C (affineLocallyFiniteType_restrict a hM)
  let : N.IsQuasicoherent := quasicoherent_of_affineCharts N (fun B k _ => (hN B k).1)
  have hflatN : relativeFlat b N := relativeFlat_pullback_of_isOpenImmersion f j hflat
  have hdim : IsLocallyConstant (moduleFiberCohomologyDimension b N q) := by
    have hc := h.comp_continuous j.continuous
    have he : modulePointFiberCohomologyDimension f M q ∘ j =
        moduleFiberCohomologyDimension b N q := by
      funext p
      exact modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension f j p M q
    rw [he] at hc
    exact hc
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom
  let := moduleCohomologyModuleOfHom W α N q
  obtain ⟨_, hp⟩ :=
    moduleCohomology_finite_projective_of_isLocallyConstant_of_proper
      (R := A) b N hN hflatN q hdim
  let : Module.Projective A (Sheaf.H.{u + 1} (moduleAddSheaf W N) q) := hp
  let Hj := H.restrict j
  let E := (higherDirectImageOpenRestrictionIso a b f j (IsPullback.of_hasPullback f j) q).app M ≪≫
    ((pushforward b).rightDerived q).mapIso C
  let EΓ := ((moduleSpecΓFunctor (R := A)).mapIso E).toLinearEquiv.trans
    (moduleHigherDirectImageAffineSectionsLinearEquiv (R := A) b N (injectiveResolution N) q)
  let : Module.Projective A ((moduleSpecΓFunctor (R := A)).obj Hj) :=
    Module.Projective.of_equiv' EΓ.symm
  let : Module.Finite A ((moduleSpecΓFunctor (R := A)).obj Hj) := (hH A j).2
  let : Hj.IsQuasicoherent := (hH A j).1
  have hLF : IsFiniteLocallyFree (Spec A) (tilde ((moduleSpecΓFunctor (R := A)).obj Hj)) :=
    finiteLocallyFree_tilde_of_finite_projective A _
  let ε : tilde ((moduleSpecΓFunctor (R := A)).obj Hj) ⟶ Hj := Hj.fromTildeΓ
  let : IsIso ε := isIso_fromTildeΓ_of_isQuasicoherent Hj
  exact finiteLocallyFree_of_iso (h := hLF) (asIso ε)

end AlgebraicGeometry.Scheme.Modules
