/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureLocality

/-! # Etale descent on a specified actual constructible partition

Finite-type local constancy on the actual base changes of a specified geometric
partition descends along any jointly surjective etale family. The construction
uses the literal cartesian squares and native module inverse images. It does
not assert that arbitrary constructible partitions upstairs descend to a
partition downstairs; that additional geometric assertion is not assumed
silently.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Descend finite-type local constancy on each original stratum along the
actual base changes of a jointly surjective etale covering family. The cover
need not be finite, and the supplied partition is the original geometric one. -/
def constructiblePartitionOfEtaleCover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (p : FiniteLocallyClosedPartition X) (F : ModuleSheaf R X)
    (hF : ∀ i k, IsFiniteTypeLocallyConstant
      ((moduleInverseImage R (pullback.fst (U i).hom (p.inclusion k))).obj
        ((moduleInverseImage R (U i).hom).obj F))) :
    ConstructiblePartition F where
  toFiniteLocallyClosedPartition := p
  locally_constant k := by
    let V (i : ι) : (p.stratum k).Etale :=
      Scheme.Etale.mk (pullback.snd (U i).hom (p.inclusion k))
    refine isFiniteTypeLocallyConstant_of_etaleCover V ?_
      ((moduleInverseImage R (p.inclusion k)).obj F) ?_
    · intro x
      obtain ⟨i, y, hy⟩ := hcover (p.inclusion k x)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
      exact ⟨i, z, hz⟩
    · intro i
      let a := pullback.fst (U i).hom (p.inclusion k)
      let b := pullback.snd (U i).hom (p.inclusion k)
      let e : (moduleInverseImage R b).obj
            ((moduleInverseImage R (p.inclusion k)).obj F) ≅
          (moduleInverseImage R a).obj ((moduleInverseImage R (U i).hom).obj F) :=
        ((moduleInverseImageComp R (p.inclusion k) b).app F).symm ≪≫
          eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F)
            (pullback.condition (f := (U i).hom) (g := p.inclusion k)).symm) ≪≫
          (moduleInverseImageComp R (U i).hom a).app F
      exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr (hF i k)

/-- Stratumwise etale descent gives actual affine-local constructibility on
a qcqs base. The common geometric partition is explicit; arbitrary upstairs
constructibility alone is not used as a substitute for that hypothesis. -/
theorem isConstructible_of_etaleCover_on_partition {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {ι : Type u}
    (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (p : FiniteLocallyClosedPartition X) (F : ModuleSheaf R X)
    (hF : ∀ i k, IsFiniteTypeLocallyConstant
      ((moduleInverseImage R (pullback.fst (U i).hom (p.inclusion k))).obj
        ((moduleInverseImage R (U i).hom).obj F))) :
    IsConstructible F := by
  let t := constructiblePartitionOfEtaleCover U hcover p F hF
  intro V
  have : IsAffine V.1.toScheme := V.property
  exact ⟨t.baseChange V.1.ι⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
