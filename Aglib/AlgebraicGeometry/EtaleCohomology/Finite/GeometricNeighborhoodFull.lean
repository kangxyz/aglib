/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFunctor

/-! # Full faithfulness of the geometric neighborhood presentation functor -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- Recover the actual base-algebra map from an affine scheme map over the base. -/
def preimageAlgHom {X Y : GeometricEtaleNeighborhood R Ω}
    (g : etaleObject R Ω Y ⟶ etaleObject R Ω X) : X.algebra →ₐ[R] Y.algebra where
  __ := (Spec.preimage g.left).hom
  commutes' r := by
    have hc : CommRingCat.ofHom (algebraMap R X.algebra) ≫ Spec.preimage g.left =
        CommRingCat.ofHom (algebraMap R Y.algebra) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact (congrArg
        (fun k : Spec (.of Y.algebra) ⟶ Spec (.of X.algebra) =>
          k ≫ Spec.algebraMap R X.algebra)
        (Spec.map_preimage g.left)).trans g.w
    exact congrArg (fun f => f.hom r) hc

variable [IsSepClosed Ω]

/-- Recover the actual pointed algebra arrow from a morphism in the original
geometric point category. -/
def preimagePointHom {X Y : GeometricEtaleNeighborhood R Ω}
    (g : (toPointElements R Ω).obj (op Y) ⟶ (toPointElements R Ω).obj (op X)) : X ⟶ Y :=
  ⟨preimageAlgHom R Ω g.hom, by
    apply AlgHom.coe_ringHom_injective
    have hc : Spec.preimage g.hom.left ≫ CommRingCat.ofHom Y.point.toRingHom =
        CommRingCat.ofHom X.point.toRingHom := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact (congrArg
        (fun k : Spec (.of Y.algebra) ⟶ Spec (.of X.algebra) =>
          Spec.map (CommRingCat.ofHom Y.point.toRingHom) ≫ k)
        (Spec.map_preimage g.hom.left)).trans (congrArg Over.Hom.left g.map_val)
    exact congrArg CommRingCat.Hom.hom hc⟩

instance : (toPointElements R Ω).Full where
  map_surjective {X Y} g := by
    refine ⟨(preimagePointHom R Ω g).op, ?_⟩
    apply Functor.Elements.Hom.ext
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_preimage _

instance : (toPointElements R Ω).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    apply AlgHom.coe_ringHom_injective
    have hc := Spec.map_injective (congrArg (fun k => k.hom.left) h)
    exact congrArg CommRingCat.Hom.hom hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
