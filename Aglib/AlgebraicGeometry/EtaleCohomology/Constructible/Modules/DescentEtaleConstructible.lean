/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleClopenPartition
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Unrestricted etale descent of constructible module coefficients

An arbitrary jointly surjective etale family can be refined by affine
source charts. Over each affine base, compactness selects finitely many
of their open images. The geometric clopen-refinement supplier produces
the required actual common partition, and finite-type local constancy
descends on its original strata. No Noetherian hypothesis on the schemes
or coefficient ring, global qcqs hypothesis, smallness assumption on the
coefficient ring, or supplied common partition is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Finitely many affine etale charts produce a downstairs partition from
their original constructible module pullbacks, rather than presupposing it. -/
theorem nonempty_constructiblePartition_of_finite_affine_etaleCover
    {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι]
    (U : ι → X.Etale) (hU : ∀ i, IsAffine (U i).left)
    (hcover : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (F : ModuleSheaf R X)
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (U i).hom).obj F)) :
    Nonempty (ConstructiblePartition F) := by
  obtain ⟨p, hp⟩ := exists_common_wholeSource_partition_of_affine_etale U hU F hF
  exact ⟨constructiblePartitionOfEtaleCover U hcover p F hp⟩

/-- On an affine base, any jointly surjective etale family with original
constructible module pullbacks supplies an actual finite partition. Only
a finite collection of actual affine subcharts is selected. -/
theorem nonempty_constructiblePartition_of_etaleCover_of_isAffine
    {X : Scheme.{u}} [IsAffine X] {ι : Type u}
    (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (F : ModuleSheaf R X)
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (U i).hom).obj F)) :
    Nonempty (ConstructiblePartition F) := by
  classical
  let I := Σ i, (U i).left.affineOpens
  let V (a : I) : X.Etale := Scheme.Etale.mk (a.2.1.ι ≫ (U a.1).hom)
  have hV (a : I) : IsAffine (V a).left := a.2.property
  let φ (a : I) : (V a).left → X := (V a).hom
  let O : I → Set X := fun a => Set.range (φ a)
  have hO (a : I) : IsOpen (O a) := (V a).hom.isOpenMap.isOpen_range
  have hc : (Set.univ : Set X) ⊆ ⋃ a : I, O a := by
    intro x _
    obtain ⟨i, y, hy⟩ := hcover x
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ (⊤ : (U i).left.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨W, hW⟩⟩, ⟨⟨y, hyW⟩, hy⟩⟩
  have hcompact : IsCompact (Set.univ : Set X) := isCompact_univ
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover O hO hc
  apply nonempty_constructiblePartition_of_finite_affine_etaleCover
    (fun a : s => V a.val) (fun a => hV a.val) ?_ F ?_
  · intro x
    obtain ⟨a, ha, y, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, y, hy⟩
  · intro a
    exact (isConstructible_iff_of_iso
      ((moduleInverseImageComp R (U a.val.1).hom a.val.2.1.ι).app F)).mpr
      (isConstructible_pullback a.val.2.1.ι (hF a.val.1))

/-- Constructibility descends through every actual jointly surjective
etale family. The family and ambient scheme need not be quasi-compact,
and the coefficient ring retains its independent universe. -/
theorem isConstructible_of_etaleCover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    {F : ModuleSheaf R X}
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (U i).hom).obj F)) :
    IsConstructible F := by
  intro V
  have : IsAffine V.1.toScheme := V.property
  let W (i : ι) : V.1.toScheme.Etale := Scheme.Etale.mk (pullback.snd (U i).hom V.1.ι)
  apply nonempty_constructiblePartition_of_etaleCover_of_isAffine W ?_
    ((moduleInverseImage R V.1.ι).obj F) ?_
  · intro x
    obtain ⟨i, y, hy⟩ := hcover (V.1.ι x)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨i, z, hz⟩
  · intro i
    let a := pullback.fst (U i).hom V.1.ι
    let b := pullback.snd (U i).hom V.1.ι
    let e : (moduleInverseImage R b).obj ((moduleInverseImage R V.1.ι).obj F) ≅
        (moduleInverseImage R a).obj ((moduleInverseImage R (U i).hom).obj F) :=
      ((moduleInverseImageComp R V.1.ι b).app F).symm ≪≫
        eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F)
          (pullback.condition (f := (U i).hom) (g := V.1.ι)).symm) ≪≫
        (moduleInverseImageComp R (U i).hom a).app F
    exact (isConstructible_iff_of_iso e).mpr (isConstructible_pullback a (hF i))

/-- The original affine-local module constructibility predicate is local
for arbitrary jointly surjective etale families. -/
theorem isConstructible_iff_etaleCover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (F : ModuleSheaf R X) :
    IsConstructible F ↔ ∀ i, IsConstructible ((moduleInverseImage R (U i).hom).obj F) :=
  ⟨fun hF i => isConstructible_pullback (U i).hom hF,
    isConstructible_of_etaleCover U hcover⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
