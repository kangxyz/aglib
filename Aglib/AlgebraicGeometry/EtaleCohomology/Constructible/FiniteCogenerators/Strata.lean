/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.ConstructibleTorsion
public import Aglib.CategoryTheory.Adjunction.MonicProducts
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Original coefficient detection on actual locally closed strata

Inverse images along a covering family of actual immersions are jointly
faithful. The proof lifts the original geometric points through these immersions
and uses the published all-coefficient stalk comparison and conservative family.

A finite locally closed partition consequently gives a literal monomorphism
from any abelian sheaf to the product of direct images of its original
restrictions. More generally, monomorphisms of these restrictions give a
monomorphism into the corresponding product of direct images by the original
adjunctions. No finiteness of the immersion morphisms is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u v

attribute [local instance] hasSheafifyLarge

/-- Actual inverse images along a covering family of immersions detect equality
of all abelian coefficient maps on the original small-etale site. -/
theorem jointlyFaithful_immersionInverseImages {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x) :
    JointlyFaithful (fun i => inverseImage (j i)) where
  map_injective {F G} a b h := by
    have (x : FibrewiseClosed.Index (𝟙 X)) : PreservesFiniteLimits
        ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
          (A := AddCommGrpCat.{u + 1})) :=
      preservesFiniteLimits_of_natIso
        (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
    apply (StalkUniverse.originalStalks_jointlyReflectIsomorphisms
      (𝟙 X)).jointlyFaithful.map_injective
    intro x
    let η := FibrewiseClosed.geometricPoint x.val
    obtain ⟨i, y, hy⟩ := hcover (η default)
    obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range (j i) η ⟨y, hy⟩
    change (pointSmallEtale η).sheafFiber.map a = (pointSmallEtale η).sheafFiber.map b
    rw [← hζ]
    let e := StalkInverseImage.stalkUnitNatIso (j i) ζ
    apply (cancel_mono (e.hom.app G)).mp
    rw [e.hom.naturality a, e.hom.naturality b]
    change e.hom.app F ≫ (pointSmallEtale ζ).sheafFiber.map ((inverseImage (j i)).map a) =
      e.hom.app F ≫ (pointSmallEtale ζ).sheafFiber.map ((inverseImage (j i)).map b)
    rw [h i]

namespace FiniteLocallyClosedPartition

variable {X : Scheme.{u}} (t : FiniteLocallyClosedPartition X)

/-- The actual stratum inverse-image functors are jointly faithful. -/
theorem jointlyFaithful_inverseImages :
    JointlyFaithful (fun i => inverseImage (t.inclusion i)) := by
  have (i : Fin t.count) : IsImmersion (t.inclusion i) := t.immersion i
  exact jointlyFaithful_immersionInverseImages t.stratum t.inclusion t.covers

/-- The finite product map obtained from actual maps on the original strata by
the original inverse-image/direct-image adjunctions. -/
def adjunctionProduct (F : AbelianSheaf.{u, u + 1} X)
    (G : ∀ i, AbelianSheaf.{u, u + 1} (t.stratum i))
    (a : ∀ i, (inverseImage (t.inclusion i)).obj F ⟶ G i) :
    F ⟶ ∏ᶜ fun i => (directImage (t.inclusion i)).obj (G i) :=
  Adjunction.adjunctionProduct (fun i => inverseImageAdjunction (t.inclusion i)) F G a

/-- Each original coordinate is exactly the adjunction unit followed by the
direct image of the supplied original stratum map. -/
@[reassoc]
theorem adjunctionProduct_π (F : AbelianSheaf.{u, u + 1} X)
    (G : ∀ i, AbelianSheaf.{u, u + 1} (t.stratum i))
    (a : ∀ i, (inverseImage (t.inclusion i)).obj F ⟶ G i) (i : Fin t.count) :
    t.adjunctionProduct F G a ≫ Pi.π (fun i => (directImage (t.inclusion i)).obj (G i)) i =
      (inverseImageAdjunction (t.inclusion i)).unit.app F ≫
        (directImage (t.inclusion i)).map (a i) :=
  Adjunction.adjunctionProduct_π (fun i => inverseImageAdjunction (t.inclusion i)) F G a i

/-- Monomorphisms on the actual covering strata give a genuine monomorphism
into the finite product of their direct images. -/
theorem mono_adjunctionProduct (F : AbelianSheaf.{u, u + 1} X)
    (G : ∀ i, AbelianSheaf.{u, u + 1} (t.stratum i))
    (a : ∀ i, (inverseImage (t.inclusion i)).obj F ⟶ G i) [∀ i, Mono (a i)] :
    Mono (t.adjunctionProduct F G a) := by
  exact Adjunction.mono_adjunctionProduct
    (fun i => inverseImageAdjunction (t.inclusion i)) F
    (fun _ _ _ h => t.jointlyFaithful_inverseImages.map_injective h) G a

/-- The literal finite product of original stratum adjunction units. -/
def unitProduct (F : AbelianSheaf.{u, u + 1} X) :
    F ⟶ ∏ᶜ fun i => (directImage (t.inclusion i)).obj
      ((inverseImage (t.inclusion i)).obj F) :=
  Adjunction.unitProduct (fun i => inverseImageAdjunction (t.inclusion i)) F

/-- Each coordinate of the stratum product is the original adjunction unit. -/
@[reassoc]
theorem unitProduct_π (F : AbelianSheaf.{u, u + 1} X) (i : Fin t.count) :
    t.unitProduct F ≫ Pi.π (fun i => (directImage (t.inclusion i)).obj
      ((inverseImage (t.inclusion i)).obj F)) i =
      (inverseImageAdjunction (t.inclusion i)).unit.app F :=
  Adjunction.unitProduct_π (fun i => inverseImageAdjunction (t.inclusion i)) F i

/-- Every actual coefficient sheaf embeds into the finite product of the
original direct images of its restrictions to the covering strata. -/
theorem mono_unitProduct (F : AbelianSheaf.{u, u + 1} X) : Mono (t.unitProduct F) := by
  exact Adjunction.mono_unitProduct
    (fun i => inverseImageAdjunction (t.inclusion i)) F
    (fun _ _ _ h => t.jointlyFaithful_inverseImages.map_injective h)

end FiniteLocallyClosedPartition
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
