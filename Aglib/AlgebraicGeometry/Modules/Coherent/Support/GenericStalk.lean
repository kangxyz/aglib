/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteLength
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Mathlib.Topology.Sober

/-!
# Finite length at generic points of coherent support

A coherent module at a minimal point of its support has finite length.
The proof uses the original module sheaf, its actual stalk, and the
canonical local spectrum; only local Noetherianity is required.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

private theorem eq_of_specializes_genericPoint {T : Type u} [TopologicalSpace T]
    [T0Space T] {x y : T} (hx : x ∈ genericPoints T) (hy : y ⤳ x) : y = x := by
  have hmax : Maximal IsIrreducible (closure ({x} : Set T)) := hx
  have hxy : closure ({x} : Set T) ⊆ closure {y} := hy.closure_subset
  have hyx : closure ({y} : Set T) ⊆ closure {x} :=
    hmax.2 isIrreducible_singleton.closure hxy
  exact (Specializes.antisymm hy (specializes_iff_closure_subset.mpr hyx)).eq

namespace AlgebraicGeometry.Scheme.Modules.Stalk

/-- A coherent module has finite-length actual stalk at a point with no
strict generalization in its support. Local Noetherianity suffices. -/
theorem finiteLength_stalk_of_minimal_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (x : X)
    (hmin : ∀ y ∈ support M, y ⤳ x → y = x) :
    IsFiniteLength (X.presheaf.stalk x) ((moduleStalk X x).obj M) := by
  classical
  let R := X.presheaf.stalk x
  let f := X.fromSpecStalk x
  let c := IsLocalRing.closedPoint R
  let N : FiniteTypeSheaves (Spec R) :=
    ⟨(Scheme.Modules.pullback f).obj M, affineLocallyFiniteType_pullback f hM⟩
  have hsupport : support N.obj ⊆ {c} := by
    intro q hq
    have hsource : f q ∈ support M := by
      by_contra h
      have hz : IsZero ((moduleStalk X (f q)).obj M) :=
        (Coherent.Support.moduleStalk_isZero_iff X M (f q)).mpr (not_not.mp h)
      let e := (pullbackModuleStalkIso f q).app M
      have he : IsZero ((moduleStalk (Spec R) q).obj N.obj) :=
        (Iso.isZero_iff e).mpr ((ModuleCat.extendScalars (f.stalkMap q).hom).map_isZero hz)
      exact hq ((Coherent.Support.moduleStalk_isZero_iff _ _ q).mp he)
    have hs : f q ⤳ x := (X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
    have heq : f q = x := hmin (f q) hsource hs
    exact f.isEmbedding.injective (heq.trans X.fromSpecStalk_closedPoint.symm)
  have hN := (affineLocallyFiniteType_spec_iff R N.obj).mp N.property
  let : N.obj.IsQuasicoherent := hN.1
  let : Module.Finite R (moduleSpecΓFunctor.obj N.obj) := hN.2
  have hsections : IsFiniteLength R (moduleSpecΓFunctor.obj N.obj) := by
    apply Module.finiteLength_of_support_maximal R (moduleSpecΓFunctor.obj N.obj)
    intro q hq
    have hq' : q ∈ support N.obj := by
      rw [support_eq_support_globalSections]
      exact hq
    have heq : q = c := hsupport hq'
    cases heq
    change (IsLocalRing.maximalIdeal R).IsMaximal
    infer_instance
  have hclosed := coherent_closedStalk_finiteLength R N hsections
  let φ := f.stalkMap c
  let : IsIso φ := fromSpecStalk_closed_stalkMap_isIso X x
  let : (ModuleCat.restrictScalars φ.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (asIso φ).commRingCatIsoToRingEquiv
  let A := (moduleStalk X (f c)).obj M
  let e := (pullbackModuleStalkIso f c).app M
  have hE : IsFiniteLength ((Spec R).presheaf.stalk c)
      ((ModuleCat.extendScalars φ.hom).obj A) := e.toLinearEquiv.isFiniteLength hclosed
  have hR : IsFiniteLength (X.presheaf.stalk (f c))
      ((ModuleCat.restrictScalars φ.hom).obj ((ModuleCat.extendScalars φ.hom).obj A)) :=
    ModuleCat.finiteLength_restrictScalars φ.hom (ConcreteCategory.bijective_of_isIso φ).2 _ hE
  let eA := asIso ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app A)
  have hA : IsFiniteLength (X.presheaf.stalk (f c)) A := eA.symm.toLinearEquiv.isFiniteLength hR
  have hc : f c = x := X.fromSpecStalk_closedPoint
  exact Eq.mp (congrArg (fun y : X => IsFiniteLength (X.presheaf.stalk y)
    ((moduleStalk X y).obj M)) hc) hA

/-- The generic points of the actual coherent support have finite-length
actual module stalks. No height filtration or auxiliary model is supplied. -/
theorem finiteLength_stalk_of_genericPoint_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (x : support M)
    (hx : x ∈ genericPoints (support M)) :
    IsFiniteLength (X.presheaf.stalk x.1) ((moduleStalk X x.1).obj M) := by
  apply finiteLength_stalk_of_minimal_support M hM x.1
  intro y hy hspec
  have hs : (⟨y, hy⟩ : support M) ⤳ x := (subtype_specializes_iff _ _).mpr hspec
  exact congrArg Subtype.val (eq_of_specializes_genericPoint hx hs)

end AlgebraicGeometry.Scheme.Modules.Stalk
