/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Hom
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Representatives


/-!
Source: `Quillen/Algebra/Homology/KInjectiveMap.lean` at frozen dirty Quillen
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `5de51324216ec5e85598159f0a8ed35543178e2d1343fb3e401f9a4fa686eaca`.
 # Additive functor action on original derived maps into K-injective targets

The genuine homotopy-to-derived Hom equivalence is inverted only at the original
K-injective target. Mapping that actual homotopy class and localizing defines an
original derived map, without exactness of the additive functor or K-injectivity
of its image. Original chain maps and composition through a K-injective middle
object are retained exactly.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- The actual derived image of an original arrow into a K-injective target. -/
def mapDerivedHomOfKInjective (K L : CochainComplex C ℤ) [L.IsKInjective]
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L) :=
  homotopyToDerivedHom _ _ ((F.mapHomotopyCategory (.up ℤ)).map
    ((homotopyDerivedHomEquiv K L).symm α))

/-- The derived action agrees with the actual image of every original chain map. -/
@[simp]
lemma mapDerivedHomOfKInjective_map (K L : CochainComplex C ℤ) [L.IsKInjective] (f : K ⟶ L) :
    mapDerivedHomOfKInjective F K L (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  unfold mapDerivedHomOfKInjective
  rw [homotopyDerivedHomEquiv_symm_map, Functor.mapHomotopyCategory_map]
  exact NatIso.naturality_1 (DerivedCategory.quotientCompQhIso D) _

/-- Actual identity arrows are preserved at K-injective objects. -/
@[simp]
lemma mapDerivedHomOfKInjective_id (K : CochainComplex C ℤ) [K.IsKInjective] :
    mapDerivedHomOfKInjective F K K (𝟙 _) = 𝟙 _ := by
  have h := mapDerivedHomOfKInjective_map F K K (𝟙 K)
  simpa using h

/-- Actual composition is retained whenever the middle and final original targets are K-injective.
-/
lemma mapDerivedHomOfKInjective_comp (K L M : CochainComplex C ℤ)
    [L.IsKInjective] [M.IsKInjective]
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)
    (β : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M) :
    mapDerivedHomOfKInjective F K M (α ≫ β) =
      mapDerivedHomOfKInjective F K L α ≫ mapDerivedHomOfKInjective F L M β := by
  obtain ⟨f, rfl⟩ := exists_chain_representative_of_isKInjective α
  obtain ⟨g, rfl⟩ := exists_chain_representative_of_isKInjective β
  rw [← CategoryTheory.Functor.map_comp, mapDerivedHomOfKInjective_map,
    mapDerivedHomOfKInjective_map, mapDerivedHomOfKInjective_map,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- Additivity is inherited from the actual homotopy-category action. -/
lemma mapDerivedHomOfKInjective_add (K L : CochainComplex C ℤ) [L.IsKInjective]
    (α β : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    mapDerivedHomOfKInjective F K L (α + β) =
      mapDerivedHomOfKInjective F K L α + mapDerivedHomOfKInjective F K L β := by
  obtain ⟨f, rfl⟩ := exists_chain_representative_of_isKInjective α
  obtain ⟨g, rfl⟩ := exists_chain_representative_of_isKInjective β
  rw [← Functor.map_add, mapDerivedHomOfKInjective_map,
    mapDerivedHomOfKInjective_map, mapDerivedHomOfKInjective_map,
    Functor.map_add, Functor.map_add]

/-- Isomorphisms between K-injective objects remain invertible under this actual derived action. -/
lemma isIso_mapDerivedHomOfKInjective (K L : CochainComplex C ℤ) [K.IsKInjective] [L.IsKInjective]
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) [IsIso α] :
    IsIso (mapDerivedHomOfKInjective F K L α) := by
  refine ⟨⟨mapDerivedHomOfKInjective F L K (inv α), ?_, ?_⟩⟩
  · rw [← mapDerivedHomOfKInjective_comp, IsIso.hom_inv_id, mapDerivedHomOfKInjective_id]
  · rw [← mapDerivedHomOfKInjective_comp, IsIso.inv_hom_id, mapDerivedHomOfKInjective_id]

end CochainComplex
