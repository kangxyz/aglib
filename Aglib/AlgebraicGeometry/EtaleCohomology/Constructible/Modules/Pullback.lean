/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.PullbackLocality

/-! # Arbitrary constructible module inverse image

For a qcqs source, finitely many affine source neighborhoods map into affine
opens of the target. Pulling back the given target partitions on these actual
affine maps and gluing them supplies a global partition on the source. Applying
this to each affine open proves constructibility of the native module inverse
image along every scheme morphism. No finiteness hypothesis is imposed on the
coefficient ring, the original morphism, or either ambient scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Actual affine source neighborhoods mapping into actual affine target
opens produce a global partition of the inverse image on a qcqs source. -/
theorem nonempty_constructiblePartition_pullback {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : S ⟶ X)
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Nonempty (ConstructiblePartition ((moduleInverseImage R f).obj F)) := by
  classical
  have hlocal (x : S) : ∃ (U : X.affineOpens) (V : S.affineOpens),
      x ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ U from hxU)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU⟩
  choose U V hxV hVU using hlocal
  apply nonempty_constructiblePartition_of_affine_neighborhoods
    ((moduleInverseImage R f).obj F)
  intro x
  refine ⟨V x, hxV x, ?_⟩
  have : IsAffine (U x).1.toScheme := (U x).property
  have : IsAffine (V x).1.toScheme := (V x).property
  let g := f.resLE (U x).1 (V x).1 (hVU x)
  obtain ⟨t⟩ := hF (U x)
  let e : (moduleInverseImage R g).obj
        ((moduleInverseImage R (U x).1.ι).obj F) ≅
      (moduleInverseImage R (V x).1.ι).obj ((moduleInverseImage R f).obj F) :=
    ((moduleInverseImageComp R (U x).1.ι g).app F).symm ≪≫
      eqToIso (congrArg (fun k => (moduleInverseImage R k).obj F)
        (f.resLE_comp_ι (hVU x))) ≪≫
      (moduleInverseImageComp R f (V x).1.ι).app F
  exact ⟨(t.baseChange g).ofIso e⟩

/-- Native inverse image preserves affine-local constructible module
coefficients along every scheme morphism, over any commutative ring. -/
theorem isConstructible_pullback {X S : Scheme.{u}} (f : S ⟶ X)
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    IsConstructible ((moduleInverseImage R f).obj F) := by
  intro U
  have : IsAffine U.1.toScheme := U.property
  obtain ⟨t⟩ := nonempty_constructiblePartition_pullback (U.1.ι ≫ f) hF
  exact ⟨t.ofIso ((moduleInverseImageComp R f U.1.ι).app F)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
