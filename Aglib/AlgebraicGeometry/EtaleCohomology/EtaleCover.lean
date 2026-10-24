/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceSheaves
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Original inverse images along jointly covering étale charts

A jointly surjective family of actual small étale objects covers the site.
The original inverse-image/slice comparison therefore detects isomorphisms
of abelian sheaves on that family. No cohomology or finiteness is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {S : Scheme.{u}} {ι : Type v} (U : ι → S.Etale)
  (hU : ∀ s : S, ∃ (i : ι) (x : (U i).left), (U i).hom x = s)

include hU

/-- Jointly surjective actual étale charts cover the original small étale site. -/
theorem etaleFamily_coversTop : S.smallEtaleTopology.CoversTop U := by
  intro W
  change Sieve.ofObjects U W ∈ S.smallGrothendieckTopology @Etale W
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  obtain ⟨i, y, hy⟩ := hU (W.hom x)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (U i).hom) (g := W.hom) y x hy
  let V : S.Etale := Scheme.Etale.mk (pullback.snd (U i).hom W.hom ≫ W.hom)
  let a : V ⟶ W :=
    MorphismProperty.Over.homMk (pullback.snd (U i).hom W.hom) rfl (by trivial)
  let b : V ⟶ U i :=
    MorphismProperty.Over.homMk (pullback.fst (U i).hom W.hom)
      pullback.condition (by trivial)
  exact ⟨V, a, z, ⟨i, ⟨b⟩⟩, inferInstance, hz₂⟩

/-- The original inverse images along a jointly surjective étale family detect
isomorphisms of arbitrary abelian sheaves. -/
theorem isIso_of_etale_inverseImages {F G : AbelianSheaf.{u, u + 1} S}
    (a : F ⟶ G) (ha : ∀ i, IsIso ((inverseImage (U i).hom).map a)) : IsIso a := by
  apply Sheaf.isIso_of_coversTop (etaleFamily_coversTop U hU)
  intro i
  let e := etaleSliceRestrictionIso (U i) ≪≫ (inverseImageEtaleIso (U i).hom).symm
  have : IsIso ((etaleSliceSheafEquivalence (U i)).inverse.map
      ((S.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1} (U i)).map a)) :=
    (NatIso.isIso_map_iff e a).mpr (ha i)
  exact isIso_of_reflects_iso
    ((S.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1} (U i)).map a)
    (etaleSliceSheafEquivalence (U i)).inverse

end AlgebraicGeometry.Scheme.EtaleCohomology
