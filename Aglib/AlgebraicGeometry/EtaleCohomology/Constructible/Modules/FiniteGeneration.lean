/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstantFiniteGeneration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Strata
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.Bounded
public import Aglib.CategoryTheory.Filtered.EventuallyEpic

/-! # Finite generation of native constructible module coefficients

On a quasi-compact scheme, affine-local constructible strata have finite-type locally constant
restrictions. Each restriction has an epimorphic original filtered stage, and
a common later stage is epimorphic by joint faithfulness. This neither replaces
the coefficient ring nor assumes finite underlying additive groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r v

variable (R : Type r) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

local instance constructibleFiniteGenerationInverseImageLeftAdjoint
    {X S : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage R f).IsLeftAdjoint := (moduleImageAdjunction R f).isLeftAdjoint

/-- Covering actual immersion inverse images are jointly faithful on native
module sheaves, through the original underlying inverse-image comparison. -/
theorem jointlyFaithful_moduleImmersionInverseImages {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x) :
    JointlyFaithful (fun i => moduleInverseImage R (j i)) where
  map_injective {F G} a b h := by
    apply (moduleUnderlying R X).map_injective
    apply (Constructible.jointlyFaithful_immersionInverseImages Y j hcover).map_injective
    intro i
    let e := moduleInverseImageUnderlyingIso R (j i)
    change (moduleUnderlying R X ⋙ inverseImage (j i)).map a =
      (moduleUnderlying R X ⋙ inverseImage (j i)).map b
    apply (cancel_epi (e.hom.app F)).mp
    rw [← e.hom.naturality a, ← e.hom.naturality b]
    change (moduleUnderlying R (Y i)).map ((moduleInverseImage R (j i)).map a) ≫ _ =
      (moduleUnderlying R (Y i)).map ((moduleInverseImage R (j i)).map b) ≫ _
    rw [h i]

/-- An actual constructible partition on a quasi-compact scheme gives an
 epimorphic original stage of any filtered colimit with that module apex. -/
theorem exists_epi_of_isColimit_of_constructiblePartition [IsNoetherianRing R]
    {X : Scheme.{u}} [CompactSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ ModuleSheaf R X} {c : Cocone D} (hc : IsColimit c)
    (t : ConstructiblePartition c.pt) : ∃ i, Epi (c.ι.app i) := by
  let (i : Fin t.count) : IsImmersion (t.inclusion i) := t.immersion i
  let (i : Fin t.count) : CompactSpace (t.stratum i) := by
    constructor
    apply (t.inclusion i).isEmbedding.isCompact_iff.mpr
    rw [Set.image_univ]
    exact isCompact_of_constructible _ (t.constructible_range i)
  apply JointlyFaithful.exists_epi_of_eventually_epi
    (fun i => moduleInverseImage R (t.inclusion i))
    (jointlyFaithful_moduleImmersionInverseImages R t.stratum t.inclusion t.covers) c
  intro i
  exact exists_epi_of_isColimit_of_isFiniteTypeLocallyConstant R
    (isColimitOfPreserves (moduleInverseImage R (t.inclusion i)) hc) (t.locally_constant i)

/-- Any actual filtered colimit with constructible module apex on a
quasi-compact scheme has an epimorphic original leg over a left Noetherian
coefficient ring. No quasi-separatedness of the base is needed. -/
theorem exists_epi_of_isColimit_of_isConstructible [IsNoetherianRing R]
    {X : Scheme.{u}} [CompactSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ ModuleSheaf R X} {c : Cocone D} (hc : IsColimit c)
    (hF : IsConstructible c.pt) : ∃ i, Epi (c.ι.app i) := by
  let a := X.affineCover.finiteSubcover
  have (i : a.I₀) : IsAffine (a.X i) := by
    change IsAffine (X.affineCover.X _)
    infer_instance
  let U (i : a.I₀) : X.affineOpens :=
    ⟨(a.f i).opensRange, isAffineOpen_opensRange (a.f i)⟩
  let (i : a.I₀) : IsAffine (U i).1.toScheme := (U i).property
  have hcover : ∀ x : X, ∃ i, ∃ y : (U i).1.toScheme, (U i).1.ι y = x := by
    intro x
    exact ⟨a.idx x, ⟨x, a.covers x⟩, rfl⟩
  apply JointlyFaithful.exists_epi_of_eventually_epi
    (fun i => moduleInverseImage R (U i).1.ι)
    (jointlyFaithful_moduleImmersionInverseImages R
      (fun i => (U i).1.toScheme) (fun i => (U i).1.ι) hcover) c
  intro i
  obtain ⟨t⟩ := hF (U i)
  exact exists_epi_of_isColimit_of_constructiblePartition R
    (isColimitOfPreserves (moduleInverseImage R (U i).1.ι) hc) t

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
