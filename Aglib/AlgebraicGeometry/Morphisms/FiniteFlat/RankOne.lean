/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Fibres
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`24f26da7d5a4f8b688ae81baa37c8db8d3136bb5077a74640de1dae06bab3c85`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules (AffineModuleBaseChange )

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
The native finite-flat rank is the dimension of the actual geometric-fibre
coordinate algebra. Consequently a finite flat morphism whose every geometric
fibre has dimension one is an isomorphism, by the pinned native rank criterion.
The optional comparison with the independent locally-free pushforward rank
uses only the explicit general sheaf base-change and fibre-rank families.
-/

/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module is a new reusable curve foundation for that application.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom.FiniteFlat
universe u
attribute [local instance] coordinateAlgebra
variable (K : Type u) [Field K] (Z : Over (Spec (.of K)))
theorem nativeRank_field (y : Spec (.of K)) [IsFinite Z.hom] [Flat Z.hom] :
    Z.hom.finrank y = Module.finrank K Γ(Z.left,⊤) := by
  letI : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let a : CommRingCat.of K ⟶ Γ(Z.left,⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ Z.hom.appTop
  have hs : Z.left.isoSpec.inv ≫ Z.hom = Spec.map a := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have hf : a.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, ← hs]
    infer_instance
  have hflat : a.hom.Flat := by
    rw [← Flat.SpecMap_iff, ← hs]
    infer_instance
  rw [← Scheme.Hom.finrank_comp_left_of_isIso Z.left.isoSpec.inv Z.hom, hs,
    Scheme.Hom.finrank_SpecMap_eq_finrank hf hflat]
  change Module.rankAtStalk (R := K) Γ(Z.left,⊤) y = Module.finrank K Γ(Z.left,⊤)
  simp [Module.rankAtStalk_eq_finrank_of_free]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
theorem nativeRank_geometricFibre (K : Type u) [Field K] (p : Spec (.of K) ⟶ Y) :
    f.finrank (p default) =
      letI : Algebra K Γ(pullback f p,⊤) := coordinateAlgebra K (Over.mk (pullback.snd f p))
      Module.finrank K Γ(pullback f p,⊤) := by
  letI : IsFinite (Over.mk (pullback.snd f p)).hom := inferInstanceAs (IsFinite (pullback.snd f p))
  letI : Flat (Over.mk (pullback.snd f p)).hom := inferInstanceAs (Flat (pullback.snd f p))
  rw [← Scheme.Hom.finrank_pullback_snd]
  exact nativeRank_field K (Over.mk (pullback.snd f p)) default

theorem nativeRank_eq_locallyFreeRank (hbase : AffineModuleBaseChange.{u}) (y : Y) :
    f.finrank y = locallyFreeRank f y := by
  let K := Y.residueField y
  let p := Y.fromSpecResidueField y
  letI : Algebra K Γ(pullback f p,⊤) := coordinateAlgebra K (Over.mk (pullback.snd f p))
  have h := nativeRank_geometricFibre f K p
  have h' : f.finrank y = Module.finrank K Γ(pullback f p,⊤) := by
    convert h using 1
    congr 1
    exact (Scheme.fromSpecResidueField_apply (X := Y) y _).symm
  exact h'.trans (moduleFibreStructureEquiv K f hbase p).finrank_eq.symm

theorem isIso_of_geometricFibre_dimension_one
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      letI : Algebra K Γ(pullback f p,⊤) := coordinateAlgebra K (Over.mk (pullback.snd f p))
      Module.finrank K Γ(pullback f p,⊤) = 1) : IsIso f := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f).mpr
  ext y
  let K := AlgebraicClosure (Y.residueField y)
  let p : Spec (.of K) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y
  have hp : p default = y := by
    change Y.fromSpecResidueField y _ = y
    exact Scheme.fromSpecResidueField_apply _ _
  change f.finrank y = 1
  rw [← hp, nativeRank_geometricFibre f K p]
  exact h K p

theorem isIso_of_hasLocallyFreeRank_one (hbase : AffineModuleBaseChange.{u})
     (hf : HasLocallyFreeRank f 1) : IsIso f := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f).mpr
  ext y
  rw [nativeRank_eq_locallyFreeRank f hbase]
  exact (hasLocallyFreeRank_iff_rank_eq f hf.finiteLocallyFree 1).mp hf y
end AlgebraicGeometry.Scheme.Hom.FiniteFlat
