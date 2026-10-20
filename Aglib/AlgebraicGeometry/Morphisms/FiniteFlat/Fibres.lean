/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Fibres` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ed596cf73cfe6e5ca63625b42fb820a24d3dd32fcb5a889304973a2d3753a7d9`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules
  (AffineModuleBaseChange  exists_sheafHasRank fieldSections
    fieldSectionsIso moduleFibre moduleFibre_finite pushforwardStructureSheaf
    sheafHasRank_iff_geometric_fibres sheafHasRank_iff_rank_eq sheafRank sheafRank_locallyConstant
    structureModuleBaseChangeMap structureModuleBaseChangeMap_isIso)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

open _root_.AlgebraicGeometry.Scheme.Modules
  (IsFiniteLocallyFree isFiniteLocallyFree_iff_exists_localBasis)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Finite locally free rank and the full geometric degree

The vector spaces are sections of actual pulled-back module sheaves and actual
geometric-fibre coordinate algebras. Their equivalence is induced by the
constructed canonical base-change map, not an arbitrary linear equivalence.
All structural field maps in the original Over-morphism count remain present.

Retained general inputs are finite-flat-finite-presentation local freeness
(02K9) and affine quasi-coherent base change for the constructed mate (02KG).
The native local-basis fibre theorem supplies the rank calculation. The finite
étale rank/count comparison, including the converse, uses these actual maps.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering7f86e4a with frozen pins.
-/
/-!
Provenance: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Mathematical-source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
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
variable (K : Type u) [Field K]
def pushforwardFieldSectionsEquiv (Z : Over (Spec (CommRingCat.of K))) :
    fieldSections K (pushforwardStructureSheaf Z.hom) ≃ₗ[K] Γ(Z.left, ⊤) :=
  LinearEquiv.refl _ _
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
def moduleFibreStructureEquiv (hbase : AffineModuleBaseChange.{u})
    [IsAffineHom f] (p : Spec (CommRingCat.of K) ⟶ Y) :
    letI : Algebra K Γ(pullback f p, ⊤) := coordinateAlgebra K (Over.mk (pullback.snd f p))
    moduleFibre K (pushforwardStructureSheaf f) p ≃ₗ[K] Γ(pullback f p, ⊤) := by
  letI : Algebra K Γ(pullback f p, ⊤) := coordinateAlgebra K (Over.mk (pullback.snd f p))
  letI := structureModuleBaseChangeMap_isIso f hbase _ p
  exact (fieldSectionsIso K (asIso (structureModuleBaseChangeMap f p))).trans
    (pushforwardFieldSectionsEquiv K (Over.mk (pullback.snd f p)))
end AlgebraicGeometry.Scheme.Hom.FiniteFlat

namespace AlgebraicGeometry.Scheme.Hom
open FiniteFlat
universe u
variable {X Y : Scheme.{u}}
/-- The actual residual-field rank function of the direct-image module sheaf. -/
def locallyFreeRank (f : X ⟶ Y) : Y → ℕ := sheafRank (pushforwardStructureSheaf f)

theorem locallyFreeRank_locallyConstant
    (f : X ⟶ Y) (hf : FiniteLocallyFree f) : IsLocallyConstant (locallyFreeRank f) := by
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hf.2
  exact sheafRank_locallyConstant (pushforwardStructureSheaf f)

theorem exists_hasLocallyFreeRank
    (f : X ⟶ Y) (hf : FiniteLocallyFree f) [ConnectedSpace Y] :
    ∃ n : ℕ, HasLocallyFreeRank f n := by
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hf.2
  obtain ⟨n, hn⟩ := exists_sheafHasRank (pushforwardStructureSheaf f)
  exact ⟨n, hf.1, hn⟩

theorem hasLocallyFreeRank_iff_rank_eq
    (f : X ⟶ Y) (hf : FiniteLocallyFree f) (n : ℕ) :
    HasLocallyFreeRank f n ↔ ∀ y, locallyFreeRank f y = n := by
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hf.2
  exact ⟨fun h ↦ (sheafHasRank_iff_rank_eq (pushforwardStructureSheaf f) n).mp h.2,
    fun h ↦ ⟨hf.1, (sheafHasRank_iff_rank_eq (pushforwardStructureSheaf f) n).mpr h⟩⟩

open AlgebraicGeometry.Scheme.OverField
variable {F : Type u} [Field F] {S T : FScheme F}
attribute [local instance] coordinateAlgebra
/-- Constant rank through actual local bases is equivalent to the original
full geometric point count, under finite étaleness. The converse is proved by
testing a geometric point above each nonempty local-basis open. -/
theorem hasLocallyFreeRank_iff_hasGeometricDegree
    (hfree : FiniteFlatPresentationLocallyFree.{u})
    (hbase : AffineModuleBaseChange.{u})
    (f : S ⟶ T) [IsFinite f.left] [Etale f.left] (n : ℕ) :
    HasLocallyFreeRank f.left n ↔ HasGeometricDegree f n := by
  have hM := finiteLocallyFree_of_finite_etale hfree f.left
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f.left) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hM.2
  rw [← hasGeometricFibreRank_iff_hasGeometricDegree]
  constructor
  · intro h K _ _ s y
    letI : Algebra K Γ(pullback f.left y.left, ⊤) := coordinateAlgebra K (geometricFibre f K s y)
    have hh := (sheafHasRank_iff_geometric_fibres (pushforwardStructureSheaf f.left) n).mp h.2
        K y.left
    exact (moduleFibreStructureEquiv K f.left hbase y.left).finrank_eq.symm.trans hh
  · intro h
    refine ⟨hM.1, (sheafHasRank_iff_geometric_fibres (pushforwardStructureSheaf f.left) n).mpr ?_⟩
    intro K _ _ p
    let s := p ≫ T.hom
    let y : Over.mk s ⟶ T := Over.homMk p rfl
    letI : Algebra K Γ(pullback f.left p, ⊤) := coordinateAlgebra K (geometricFibre f K s y)
    exact (moduleFibreStructureEquiv K f.left hbase p).finrank_eq.trans (h K s y)
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom.FiniteFlat
universe u
variable (K : Type u) [Field K] {X Y T : Scheme.{u}}
def moduleFibreIso {M N : Y.Modules} (e : M ≅ N)
    (p : Spec (CommRingCat.of K) ⟶ Y) :
    moduleFibre K M p ≃ₗ[K] moduleFibre K N p :=
  fieldSectionsIso K ((Scheme.Modules.pullback p).mapIso e)

def moduleFibrePullbackIso (M : Y.Modules) (g : T ⟶ Y)
    (p : Spec (CommRingCat.of K) ⟶ T) :
    moduleFibre K ((Scheme.Modules.pullback g).obj M) p ≃ₗ[K]
      moduleFibre K M (p ≫ g) :=
  fieldSectionsIso K ((Scheme.Modules.pullbackComp p g).app M)
end AlgebraicGeometry.Scheme.Hom.FiniteFlat

namespace AlgebraicGeometry.Scheme.Hom
open FiniteFlat
universe u
variable {X Y T : Scheme.{u}}
/-- Base change preserves constant sheaf rank for finite étale morphisms,
by actual module base-change and pullback composition isomorphisms. -/
theorem hasLocallyFreeRank_baseChange
    (hfree : FiniteFlatPresentationLocallyFree.{u})
    (hbase : AffineModuleBaseChange.{u})
    (f : X ⟶ Y) [IsFinite f] [Etale f] (g : T ⟶ Y)
    (n : ℕ) (hf : HasLocallyFreeRank f n) :
    HasLocallyFreeRank (pullback.snd f g) n := by
  have hM := finiteLocallyFree_of_finite_etale hfree f
  have hM' := finiteLocallyFree_of_finite_etale hfree (pullback.snd f g)
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hM.2
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf (pullback.snd f g)) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hM'.2
  have hr := (sheafHasRank_iff_geometric_fibres (pushforwardStructureSheaf f) n).mp hf.2
  haveI := structureModuleBaseChangeMap_isIso f hbase T g
  let e := asIso (structureModuleBaseChangeMap f g)
  refine ⟨hM'.1, (sheafHasRank_iff_geometric_fibres (pushforwardStructureSheaf (pullback.snd f
      g)) n).mpr ?_⟩
  intro K _ _ p
  exact (moduleFibreIso K e p).finrank_eq.symm.trans
    ((moduleFibrePullbackIso K (pushforwardStructureSheaf f) g p).finrank_eq.trans
      (hr K (p ≫ g)))
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
open FiniteFlat
universe u
variable {X Y : Scheme.{u}}
/-- A finite surjective map has positive local-free rank at every point.
This uses the actual nonempty scheme-theoretic fibre, not reduced point counts. -/
theorem locallyFreeRank_pos_of_surjective
    (hbase : AffineModuleBaseChange.{u})
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (hf : FiniteLocallyFree f) (y : Y) :
    0 < locallyFreeRank f y := by
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hf.2
  let K := Y.residueField y
  let p := Y.fromSpecResidueField y
  let Z := Over.mk (pullback.snd f p)
  letI : Algebra K Γ(pullback f p, ⊤) := coordinateAlgebra K Z
  obtain ⟨x, _⟩ := (pullback.snd f p).surjective (default : Spec (CommRingCat.of K))
  letI : Nonempty (⊤ : (pullback f p).Opens) := ⟨⟨x, trivial⟩⟩
  let e := moduleFibreStructureEquiv K f hbase p
  letI := moduleFibre_finite (pushforwardStructureSheaf f) K p
  letI : Module.Finite K Γ(pullback f p, ⊤) := Module.Finite.of_surjective e.toLinearMap
      e.surjective
  have he : Module.finrank K Γ(pullback f p, ⊤) = locallyFreeRank f y := e.finrank_eq.symm
  rw [← he]
  exact Module.finrank_pos
end AlgebraicGeometry.Scheme.Hom
