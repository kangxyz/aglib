/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback

/-! # Zariski descent of constructible module coefficients

Constructibility can be checked on any actual open cover. Neither the ambient
scheme nor the cover is required to be finite or quasi-compact: only each
affine test uses a finite affine subcover and an actual glued partition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r v

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- On a qcqs scheme, constructibility on any open cover produces a global
actual partition. Finiteness is supplied by affine-neighborhood compactness. -/
theorem nonempty_constructiblePartition_of_open_cover {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {ι : Type v} (U : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {F : ModuleSheaf R X}
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (U i).ι).obj F)) :
    Nonempty (ConstructiblePartition F) := by
  apply nonempty_constructiblePartition_of_affine_neighborhoods F
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxi
  refine ⟨⟨V, hV⟩, hxV, ?_⟩
  have : IsAffine V.toScheme := hV
  let g := X.homOfLE hVU
  obtain ⟨t⟩ := nonempty_constructiblePartition (isConstructible_pullback g (hF i))
  let e : (moduleInverseImage R g).obj ((moduleInverseImage R (U i).ι).obj F) ≅
      (moduleInverseImage R V.ι).obj F :=
    ((moduleInverseImageComp R (U i).ι g).app F).symm ≪≫
      eqToIso (congrArg (fun k => (moduleInverseImage R k).obj F) (X.homOfLE_ι hVU))
  exact ⟨t.ofIso e⟩

/-- Constructibility descends through any jointly covering family of open
subschemes, with no finiteness condition on the family or ambient scheme. -/
theorem isConstructible_of_open_cover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {F : ModuleSheaf R X}
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (U i).ι).obj F)) :
    IsConstructible F := by
  intro V
  have : IsAffine V.1.toScheme := V.property
  apply nonempty_constructiblePartition_of_open_cover (fun i => V.1.ι ⁻¹ᵁ U i)
    (fun x => hcover x.1)
  intro i
  let g := V.1.ι ∣_ U i
  let e : (moduleInverseImage R g).obj ((moduleInverseImage R (U i).ι).obj F) ≅
      (moduleInverseImage R (V.1.ι ⁻¹ᵁ U i).ι).obj ((moduleInverseImage R V.1.ι).obj F) :=
    ((moduleInverseImageComp R (U i).ι g).app F).symm ≪≫
      eqToIso (congrArg (fun k => (moduleInverseImage R k).obj F)
        (morphismRestrict_ι V.1.ι (U i))) ≪≫
      (moduleInverseImageComp R V.1.ι (V.1.ι ⁻¹ᵁ U i).ι).app F
  exact (isConstructible_iff_of_iso e).mp (isConstructible_pullback g (hF i))

/-- The original affine-local module predicate is local for arbitrary actual
Zariski open covers. -/
theorem isConstructible_iff_open_cover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (F : ModuleSheaf R X) :
    IsConstructible F ↔ ∀ i, IsConstructible ((moduleInverseImage R (U i).ι).obj F) :=
  ⟨fun hF i => isConstructible_pullback (U i).ι hF,
    isConstructible_of_open_cover U hcover⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
