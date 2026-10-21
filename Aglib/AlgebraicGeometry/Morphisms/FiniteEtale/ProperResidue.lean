/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverEpimorphisms
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# Faithfulness on the actual closed fibre of a universally closed model

Over a commutative local ring, maps between finite etale covers of a
universally closed model are determined by their literal closed-fibre
restrictions. The target is unramified over the model, while the model
need not be unramified or smooth. The base need not be Henselian or Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (p : X ⟶ Y)

/-- The literal two-step pullback meets exactly those points whose image in
the local spectrum is in the actual residue-map range. -/
theorem mem_range_cover_projection_iff (x : X) :
    x ∈ Set.range (pullback.fst p (projection π)) ↔
      (p ≫ π) x ∈ Set.range (residueSpecMap R) := by
  rw [Scheme.Pullback.range_fst]
  change p x ∈ Set.range (pullback.fst π (residueSpecMap R)) ↔ _
  rw [Scheme.Pullback.range_fst]
  rfl

/-- Both original pullback squares commute after passing to the local base. -/
@[reassoc]
theorem cover_projection_residue_square :
    pullback.fst p (projection π) ≫ p ≫ π =
      pullback.snd p (projection π) ≫ pullback.snd π (residueSpecMap R) ≫
        residueSpecMap R := by
  rw [← Category.assoc, pullback.condition, Category.assoc]
  exact congrArg (fun h => pullback.snd p (projection π) ≫ h)
    (pullback.condition (f := π) (g := residueSpecMap R))

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

namespace AlgebraicGeometry.Scheme.Hom

variable (R : Type u) [CommRing R] [IsLocalRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Maps to a relatively unramified target are determined by closed-fibre
restriction when their source is universally closed over the local base.
Unramifiedness is required over the model, not over the local spectrum. -/
theorem eq_of_closedFiber_pullback_eq {X Y Z : Scheme.{u}}
    (π : Y ⟶ Spec (.of R)) (p : X ⟶ Y) [UniversallyClosed (p ≫ π)]
    (q : Z ⟶ Y) [FormallyUnramified q] [LocallyOfFiniteType q]
    (f g : X ⟶ Z) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (hr : pullback.fst p (LocalRing.ResidueFiber.projection π) ≫ f =
      pullback.fst p (LocalRing.ResidueFiber.projection π) ≫ g) : f = g := by
  classical
  let i := pullback.fst p (LocalRing.ResidueFiber.projection π)
  let a : X ⟶ pullback q q := pullback.lift f g (hf.trans hg.symm)
  let j : pullback a (pullback.diagonal q) ⟶ X := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hia : i ≫ a = (i ≫ f) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp [a]
    · simpa [a] using hr.symm
  let l : pullback p (LocalRing.ResidueFiber.projection π) ⟶
      pullback a (pullback.diagonal q) := pullback.lift i (i ≫ f) hia
  have hlj : l ≫ j = i := by simp [l, j]
  have hclosed : IsClosed ((p ≫ π) '' (Set.range j)ᶜ) :=
    (p ≫ π).isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl
  have hclosedPoint : IsLocalRing.closedPoint R ∈ Set.range (LocalRing.residueSpecMap R) := by
    refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  have hjsurj : Surjective j := by
    constructor
    intro x
    by_contra hx
    have hximage : (p ≫ π) x ∈ (p ≫ π) '' (Set.range j)ᶜ := ⟨x, hx, rfl⟩
    have hm : IsLocalRing.closedPoint R ∈ (p ≫ π) '' (Set.range j)ᶜ :=
      (IsLocalRing.specializes_closedPoint ((p ≫ π) x)).mem_closed hclosed hximage
    obtain ⟨z, hz, hzm⟩ := hm
    have hzi : z ∈ Set.range i := by
      apply (LocalRing.ResidueFiber.mem_range_cover_projection_iff π p z).mpr
      rwa [hzm]
    obtain ⟨w, hw⟩ := hzi
    exact hz ⟨l w, (congrArg
      (fun t : pullback p (LocalRing.ResidueFiber.projection π) ⟶ X => t w) hlj).trans hw⟩
  have : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, hjsurj⟩
  apply (cancel_epi j).mp
  have hj : j ≫ a = pullback.snd a (pullback.diagonal q) ≫ pullback.diagonal q :=
    pullback.condition
  calc
    j ≫ f = (j ≫ a) ≫ pullback.fst q q := by simp [a]
    _ = (pullback.snd a (pullback.diagonal q) ≫ pullback.diagonal q) ≫
        pullback.fst q q := by rw [hj]
    _ = pullback.snd a (pullback.diagonal q) := by simp
    _ = (pullback.snd a (pullback.diagonal q) ≫ pullback.diagonal q) ≫
        pullback.snd q q := by simp
    _ = (j ≫ a) ≫ pullback.snd q q := by rw [hj]
    _ = j ≫ g := by simp [a]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual closed-fibre pullback on finite etale covers of a universally
closed model over a local ring is faithful. In particular this applies to
proper models, without requiring smoothness of the model morphism. -/
instance closedFiber_baseChange_faithful [UniversallyClosed π] :
    (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).Faithful where
  map_injective := by
    intro X Z f g h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Hom.eq_of_closedFiber_pullback_eq R π X.obj.hom Z.obj.hom
      f.hom.left g.hom.left (Over.w f.hom) (Over.w g.hom)
    calc
      pullback.fst X.obj.hom (LocalRing.ResidueFiber.projection π) ≫ f.hom.left =
          ((baseChange (LocalRing.ResidueFiber.projection π)).map f).hom.left ≫
            pullback.fst Z.obj.hom (LocalRing.ResidueFiber.projection π) :=
        (pullback.lift_fst _ _ _).symm
      _ = ((baseChange (LocalRing.ResidueFiber.projection π)).map g).hom.left ≫
          pullback.fst Z.obj.hom (LocalRing.ResidueFiber.projection π) :=
        congrArg (fun k => k.hom.left ≫
          pullback.fst Z.obj.hom (LocalRing.ResidueFiber.projection π)) h
      _ = pullback.fst X.obj.hom (LocalRing.ResidueFiber.projection π) ≫ g.hom.left :=
        pullback.lift_fst _ _ _

/-- The same actual closed-fibre functor detects isomorphisms. Faithfulness
reflects monomorphisms and epimorphisms, and actual finite etale covers form
a balanced category. -/
instance closedFiber_baseChange_reflectsIsomorphisms [UniversallyClosed π] :
    (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).ReflectsIsomorphisms where
  reflects f _ := by
    let F := baseChange (pullback.fst π (LocalRing.residueSpecMap R))
    have : Mono f := F.mono_of_mono_map (by infer_instance)
    have : Epi f := F.epi_of_epi_map (by infer_instance)
    exact cover_isIso_of_mono_epi f

/-- The forward cover retains the actual second pullback projection. -/
@[simp] theorem baseChange_obj_hom (X : FiniteEtale Y) :
    ((baseChange (LocalRing.ResidueFiber.projection π)).obj X).obj.hom =
      pullback.snd X.obj.hom (pullback.fst π (LocalRing.residueSpecMap R)) := rfl

/-- The forward map commutes with the original first pullback projections. -/
@[reassoc] theorem baseChange_map_fst {X Z : FiniteEtale Y} (f : X ⟶ Z) :
    ((baseChange (LocalRing.ResidueFiber.projection π)).map f).hom.left ≫
        pullback.fst Z.obj.hom (LocalRing.ResidueFiber.projection π) =
      pullback.fst X.obj.hom (LocalRing.ResidueFiber.projection π) ≫ f.hom.left :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue
