/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.LocalPullback
public import Aglib.AlgebraicGeometry.Modules.Stalk.FiniteLength
public import Aglib.AlgebraicGeometry.Modules.Coherent.StalkFinite
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StratumQuotient
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian

/-!
# Finite-length landing of coherent height stalks

Source-only extraction from `R5Lab.KTheory.Quillen.CoherentLengthLanding` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.FiniteLength` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8eb35f2789881b564ff489ef60ea88e43b78d26926fdd5fa7d477b3fb87852c3`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
attribute [local instance] Abelian.hasFiniteBiproducts
open ModuleCat.FiniteLengthFamilies CategoryTheory.Pi
namespace AlgebraicGeometry.Scheme.Modules.Stalk
universe u

/-- The canonical stalk map at the closed point of the actual local spectrum is
an isomorphism, from the literal stalkClosedPointTo/fromSpecStalk identity. -/
theorem fromSpecStalk_closed_stalkMap_isIso (X : Scheme.{u}) (x : X) :
    IsIso ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint (X.presheaf.stalk x))) := by
  let R := X.presheaf.stalk x
  let f := X.fromSpecStalk x
  have ht : IsIso (Scheme.stalkClosedPointTo f) := by
    dsimp [f]
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  have he : f.stalkMap (IsLocalRing.closedPoint R) =
      Scheme.stalkClosedPointTo f ≫ (stalkClosedPointIso R).inv := by
    simp [Scheme.stalkClosedPointTo, R]
  rw [he]
  infer_instance

/-- Actual finite-length landing for every height p on every Noetherian scheme.
The local module is the original stalk, with no finite-length input. -/
theorem coherent_height_stalk_finiteLength (X : Scheme.{u}) [IsNoetherian X]
    (p : ℕ) (M : CohAtLeast X p) (x : HeightPoint X p) :
    IsFiniteLength (X.presheaf.stalk x.1)
      ((Scheme.Modules.moduleStalk X x.1).obj M.obj.obj) := by
  let R := X.presheaf.stalk x.1
  let c := IsLocalRing.closedPoint R
  let f := X.fromSpecStalk x.1
  let N := localCoherentPullback X p M x
  have hN := coherent_closedStalk_finiteLength R N
    (local_pullback_sections_finiteLength X p M x)
  let φ := f.stalkMap c
  let : IsIso φ := fromSpecStalk_closed_stalkMap_isIso X x.1
  let : (ModuleCat.restrictScalars φ.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (asIso φ).commRingCatIsoToRingEquiv
  let A := (Scheme.Modules.moduleStalk X (f c)).obj M.obj.obj
  let e := (Scheme.Modules.pullbackModuleStalkIso f c).app M.obj.obj
  have hE : IsFiniteLength ((Spec R).presheaf.stalk c)
      ((ModuleCat.extendScalars φ.hom).obj A) := e.toLinearEquiv.isFiniteLength hN
  have hR : IsFiniteLength (X.presheaf.stalk (f c))
      ((ModuleCat.restrictScalars φ.hom).obj ((ModuleCat.extendScalars φ.hom).obj A)) :=
    ModuleCat.finiteLength_restrictScalars φ.hom (ConcreteCategory.bijective_of_isIso φ).2 _ hE
  let eA := asIso ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app A)
  have hA : IsFiniteLength (X.presheaf.stalk (f c)) A := eA.symm.toLinearEquiv.isFiniteLength hR
  have hc : f c = x.1 := X.fromSpecStalk_closedPoint
  exact Eq.mp (congrArg (fun y : X => IsFiniteLength (X.presheaf.stalk y)
    ((Scheme.Modules.moduleStalk X y).obj M.obj.obj)) hc) hA

/-- The exact functor of actual coherent stalks into genuine finite-length local
module families. Finite support and finite length are both supplied by proofs. -/
def lengthStalks (X : Scheme.{u}) [IsNoetherian X] (p : ℕ) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohAtLeast X p))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Family (localRings X p))) where
  toFunctor := (familyProperty (localRings X p)).lift
    ((coherentAtLeast X p).ι ⋙ (allStratumStalks X p).toFunctor)
    (fun M => ⟨coherent_height_stalk_finiteLength X p M, stratumStalks_finite X p M⟩)
  additive := {
    map_add := by
      intros
      apply (familyProperty (localRings X p)).ι.map_injective
      funext x
      exact (coherentStalk X x.1).toFunctor.map_add }
  map_conflation S h := by
    let P := familyProperty (localRings X p)
    let F := (_root_.CategoryTheory.ObjectProperty.exactInclusion (coherentAtLeast X p)).comp
        (allStratumStalks X p)
    have he := F.map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful P.ι _ he.exact
            mono_f := P.ι.mono_of_mono_map he.mono_f
            epi_g := P.ι.epi_of_epi_map he.epi_g }

/-- Forgetting only the proved length property recovers the maintained stalk functor strictly. -/
theorem lengthStalks_forget (X : Scheme.{u}) [IsNoetherian X] (p : ℕ) :
    (lengthStalks X p).toFunctor ⋙
      (familyProperty (localRings X p)).ιOfLE (fun _ h => h.2) =
      (stratumStalks X p).toFunctor := rfl

end AlgebraicGeometry.Scheme.Modules.Stalk
