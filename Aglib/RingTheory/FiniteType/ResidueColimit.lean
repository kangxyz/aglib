/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue fields of finitely generated subalgebras

For a maximal ideal of an algebra, its residue field is the filtered colimit
of the residue fields at its inverse-image primes in the finite-generated
subalgebras. All arrows are the native marked residue-field maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Algebra.FiniteTypeSubalgebraLimit

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
variable (p : Ideal A) [p.IsPrime]

/-- The prime selected by the original prime of the full algebra. -/
def stagePrime (s : Finset A) : Ideal (stage R A s) :=
  p.comap (stage R A s).val.toRingHom

instance stagePrime_isPrime (s : Finset A) : (stagePrime R A p s).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The actual inclusion between two finite-generated stages. -/
def stageInclusion {s t : Finset A} (f : s ⟶ t) :
    stage R A s →ₐ[R] stage R A t :=
  Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom f)))

/-- The native residue-field arrow between two selected stage primes. -/
def residueTransition {s t : Finset A} (f : s ⟶ t) :
    (stagePrime R A p s).ResidueField →+* (stagePrime R A p t).ResidueField :=
  Ideal.ResidueField.map _ _ (stageInclusion R A f).toRingHom rfl

/-- The canonical embedding of each stage residue field into the original one. -/
def residueInclusion (s : Finset A) :
    (stagePrime R A p s).ResidueField →+* p.ResidueField :=
  Ideal.ResidueField.map _ _ (stage R A s).val.toRingHom rfl

@[simp]
theorem residueTransition_algebraMap {s t : Finset A} (f : s ⟶ t)
    (x : stage R A s) :
    residueTransition R A p f (algebraMap _ _ x) =
      algebraMap (stage R A t) (stagePrime R A p t).ResidueField
        (stageInclusion R A f x) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ x

@[simp]
theorem residueInclusion_algebraMap (s : Finset A) (x : stage R A s) :
    residueInclusion R A p s (algebraMap _ _ x) = algebraMap A p.ResidueField x :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ x

/-- The diagram uses the specified primes, not arbitrary isomorphic fields. -/
def residueDiagram : Finset A ⥤ CommRingCat.{v} where
  obj s := CommRingCat.of (stagePrime R A p s).ResidueField
  map f := CommRingCat.ofHom (residueTransition R A p f)
  map_id s := by
    apply CommRingCat.hom_ext
    change residueTransition R A p (𝟙 s) = RingHom.id _
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, residueTransition_algebraMap, RingHom.id_apply]
    rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    change residueTransition R A p (f ≫ g) =
      (residueTransition R A p g).comp (residueTransition R A p f)
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, residueTransition_algebraMap]
    rfl

/-- The marked residue-field inclusion cocone. -/
def residueCocone : Cocone (residueDiagram R A p) where
  pt := CommRingCat.of p.ResidueField
  ι :=
    { app s := CommRingCat.ofHom (residueInclusion R A p s)
      naturality s t f := by
        apply CommRingCat.hom_ext
        change (residueInclusion R A p t).comp (residueTransition R A p f) =
          residueInclusion R A p s
        apply Ideal.ResidueField.ringHom_ext
        ext x
        simp only [RingHom.comp_apply, residueTransition_algebraMap,
          residueInclusion_algebraMap]
        rfl }

/-- The underlying type-valued residue-field cocone. -/
def residueTypeCocone : (residueDiagram R A p ⋙ forget CommRingCat).CoconeTypes :=
  (residueDiagram R A p ⋙ forget CommRingCat).coconeTypesEquiv.symm
    ((forget CommRingCat).mapCocone (residueCocone R A p))

variable [p.IsMaximal]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Residue-field embeddings are injective, and every original residue has a
representative at a singleton-generated stage. -/
theorem residueTypeCocone_isColimit : (residueTypeCocone R A p).IsColimit := by
  refine ⟨?_, ?_⟩
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered']
    intro s x y h
    refine ⟨s, 𝟙 s, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    change x = y
    exact (residueInclusion R A p s).injective h
  · intro x
    obtain ⟨a, rfl⟩ := p.algebraMap_residueField_surjective x
    refine ⟨Functor.ιColimitType (residueDiagram R A p ⋙ forget CommRingCat) {a}
      (algebraMap (stage R A {a}) (stagePrime R A p {a}).ResidueField
        (singleElement R A a)), ?_⟩
    rw [Functor.descColimitType_ιColimitType_apply]
    exact residueInclusion_algebraMap R A p {a} (singleElement R A a)

/-- The original residue field is the colimit of the selected residue fields. -/
def residueCoconeIsColimit : IsColimit (residueCocone R A p) := by
  let : ReflectsColimit (residueDiagram R A p) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat)
  exact ((Functor.CoconeTypes.isColimit_iff (residueTypeCocone R A p)).mp
    (residueTypeCocone_isColimit R A p)).some

end Algebra.FiniteTypeSubalgebraLimit
