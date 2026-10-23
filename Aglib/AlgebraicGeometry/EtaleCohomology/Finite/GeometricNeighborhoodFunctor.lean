/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodLimit
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Geometric algebra neighborhoods in the original small etale point category

The small algebra-presentation index maps to the native category of elements
used to define the original geometric stalk. Both its scheme morphisms and
chosen points are literal spectrum maps. Initiality is a separate theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The actual small-etale object associated to an algebra neighborhood. -/
def etaleObject (X : GeometricEtaleNeighborhood R Ω) : (Spec (.of R)).Etale := by
  let : Etale (Spec.algebraMap R X.algebra) :=
    (HasRingHomProperty.Spec_iff (P := @Etale.{u})).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact Scheme.Etale.mk (Spec.algebraMap R X.algebra)

/-- The algebra neighborhood's specified point is over the original base point. -/
lemma stagePoint_over (X : GeometricEtaleNeighborhood R Ω) :
    Spec.map (CommRingCat.ofHom X.point.toRingHom) ≫ (etaleObject R Ω X).hom =
      Spec.algebraMap R Ω := by
  change Spec.map (CommRingCat.ofHom X.point.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R X.algebra)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) X.point.comp_algebraMap

/-- An algebra arrow induces the literal opposite scheme arrow over the base. -/
def etaleMap {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    etaleObject R Ω Y ⟶ etaleObject R Ω X :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom f.val.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R X.algebra)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) f.val.comp_algebraMap)

variable [IsSepClosed Ω]

/-- The literal chosen geometric point in the native point-fiber functor. -/
def stagePoint (X : GeometricEtaleNeighborhood R Ω) :
    (pointSmallEtale (Spec.algebraMap R Ω)).fiber.obj (etaleObject R Ω X) :=
  Over.homMk (Spec.map (CommRingCat.ofHom X.point.toRingHom)) (stagePoint_over R Ω X)

/-- The actual small presentation index maps into the original stalk index,
without replacing its objects, points, or transition maps by an abstract model. -/
def toPointElements : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤
    (pointSmallEtale (Spec.algebraMap R Ω)).fiber.Elements where
  obj X := Functor.elementsMk _ (etaleObject R Ω X.unop) (stagePoint R Ω X.unop)
  map {X Y} f :=
    { hom := etaleMap R Ω f.unop
      map_val := by
        apply Over.OverMorphism.ext
        change Spec.map (CommRingCat.ofHom X.unop.point.toRingHom) ≫
          Spec.map (CommRingCat.ofHom f.unop.val.toRingHom) =
            Spec.map (CommRingCat.ofHom Y.unop.point.toRingHom)
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
          (congrArg AlgHom.toRingHom f.unop.property) }
  map_id X := by
    apply Functor.Elements.Hom.ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (AlgHom.id R X.unop.algebra).toRingHom) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    apply Functor.Elements.Hom.ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (f.unop.val.comp g.unop.val).toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.val.toRingHom)
    change Spec.map (CommRingCat.ofHom g.unop.val.toRingHom ≫
      CommRingCat.ofHom f.unop.val.toRingHom) = _
    exact Spec.map_comp _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
