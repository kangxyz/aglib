/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleCover

/-! # Conservativity of actual module inverse image on etale covers

The original abelian cover-conservativity theorem applies to the actual
underlying module coefficient through its native inverse-image comparison.
Native sheaf separatedness makes inverse image along a surjective etale
morphism faithful, and hence able to reflect monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u v r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

local instance coverConservativityHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, r}

/-- Actual inverse images on a jointly surjective etale family detect
isomorphisms of the original module sheaves. -/
theorem isIso_of_module_etale_inverseImages {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Etale)
    (hU : ∀ x : X, ∃ (i : ι) (y : (U i).left), (U i).hom y = x)
    {F G : ModuleSheaf R X} (a : F ⟶ G)
    (ha : ∀ i, IsIso ((moduleInverseImage R (U i).hom).map a)) : IsIso a := by
  have : IsIso ((moduleUnderlying R X).map a) := by
    apply isIso_of_etale_inverseImages U hU
    intro i
    have : IsIso ((moduleInverseImage R (U i).hom).map a) := ha i
    apply (NatIso.isIso_map_iff (moduleInverseImageUnderlyingIso R (U i).hom) a).mp
    change IsIso ((moduleUnderlying R (U i).left).map
      ((moduleInverseImage R (U i).hom).map a))
    infer_instance
  exact isIso_of_reflects_iso a (moduleUnderlying R X)

/-- Native module inverse image along a surjective etale morphism is faithful. -/
instance moduleInverseImage_faithful_of_surjective {X S : Scheme.{u}}
    (f : S ⟶ X) [Etale f] [Surjective f] : (moduleInverseImage R f).Faithful where
  map_injective {F G} {a b} hab := by
    let U : X.Etale := Scheme.Etale.mk f
    let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙
        (moduleEtaleSliceEquivalence R U).inverse ≅ moduleInverseImage R f :=
      moduleEtaleSliceRestrictionIso R U ≪≫ (moduleInverseImageEtaleIso R f).symm
    have hslice : (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).map a =
        (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U).map b := by
      apply (moduleEtaleSliceEquivalence R U).inverse.map_injective
      change (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙
          (moduleEtaleSliceEquivalence R U).inverse).map a =
        (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙
          (moduleEtaleSliceEquivalence R U).inverse).map b
      apply (cancel_mono (e.hom.app G)).mp
      rw [e.hom.naturality a, e.hom.naturality b]
      exact congrArg (fun q : (moduleInverseImage R f).obj F ⟶
        (moduleInverseImage R f).obj G => e.hom.app F ≫ q) hab
    let V : Unit → X.Etale := fun _ => U
    have hV : X.smallEtaleTopology.CoversTop V := by
      apply etaleFamily_coversTop V
      intro x
      obtain ⟨y, hy⟩ := f.surjective x
      exact ⟨(), y, hy⟩
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    refine G.property.hom_ext (hV.cover W.unop) _ _ fun I => ?_
    obtain ⟨i, ⟨g⟩⟩ := I.hf
    have h := congrArg (fun q => q.hom.app (Opposite.op (Over.mk g))) hslice
    change a.hom.app (Opposite.op I.Y) = b.hom.app (Opposite.op I.Y) at h
    rw [← a.hom.naturality, ← b.hom.naturality, h]

/-- A map of original module sheaves is monic exactly when its actual inverse
image along a surjective etale morphism is monic. -/
theorem moduleInverseImage_mono_iff_of_surjective {X S : Scheme.{u}}
    (f : S ⟶ X) [Etale f] [Surjective f] {F G : ModuleSheaf R X} (a : F ⟶ G) :
    Mono ((moduleInverseImage R f).map a) ↔ Mono a := by
  constructor
  · exact (moduleInverseImage R f).mono_of_mono_map
  · intro ha
    have : Mono a := ha
    infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
