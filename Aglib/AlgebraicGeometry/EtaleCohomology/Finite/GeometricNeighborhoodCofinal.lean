/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFull
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Initiality of the geometric etale presentation index -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- Every pointed etale scheme over the affine base receives an actual pointed
map from a small algebra-presentation neighborhood. -/
theorem exists_stage_map (U : (Spec (.of R)).Etale) (y : Spec (.of Ω) ⟶ U.left)
    (hy : y ≫ U.hom = Spec.algebraMap R Ω) :
    ∃ (X : GeometricEtaleNeighborhood R Ω) (a : Spec (.of X.algebra) ⟶ U.left),
      a ≫ U.hom = Spec.algebraMap R X.algebra ∧
      Spec.map (CommRingCat.ofHom X.point.toRingHom) ≫ a = y := by
  let : Etale U.hom := U.prop
  obtain ⟨A, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := y.base default) (U := ⊤) (by simp)
  have hrange : Set.range y.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x default]
  let y' := IsOpenImmersion.lift j y hrange
  have hy' : y' ≫ j = y := IsOpenImmersion.lift_fac j y hrange
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ U.hom)
  let : Algebra R A := g.hom.toAlgebra
  have hcoord : Spec.algebraMap R A = j ≫ U.hom := hg
  let : Algebra.Etale R A := by
    have he : Etale (Spec.algebraMap R A) := by rw [hcoord]; infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  have hc : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage y' =
      CommRingCat.ofHom (algebraMap R Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    change y' ≫ Spec.algebraMap R A = Spec.algebraMap R Ω
    rw [hcoord, ← Category.assoc, hy', hy]
  let p : A →ₐ[R] Ω :=
    { (Spec.preimage y').hom with commutes' r := congrArg (fun f => f.hom r) hc }
  obtain ⟨X, e, he⟩ := GeometricEtaleNeighborhood.exists_equiv A p
  refine ⟨X, Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hcoord]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) e.toAlgHom.comp_algebraMap
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hp : X.point.toRingHom.comp e.toRingHom = p.toRingHom :=
      congrArg AlgHom.toRingHom he
    rw [hp]
    change Spec.map (Spec.preimage y') ≫ j = y
    rw [Spec.map_preimage, hy']

/-- The actual algebra presentation functor is initial in the original
geometric point category. In particular, its opposite computes original stalks. -/
instance toPointElements_initial : (toPointElements R Ω).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro d
  obtain ⟨y, hy, hyEq⟩ := Over.homMk_surjective d.val
  obtain ⟨X, a, ha, hpoint⟩ := exists_stage_map R Ω d.obj y hy
  refine ⟨op X, ⟨?_⟩⟩
  refine { hom := MorphismProperty.Over.homMk a ha, map_val := ?_ }
  apply Over.OverMorphism.ext
  exact hpoint.trans (congrArg Over.Hom.left hyEq).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
