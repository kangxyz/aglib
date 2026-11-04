/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCoefficients
public import Mathlib.CategoryTheory.Sites.EpiMono

/-! Epimorphisms of original represented coefficients on the small étale site. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

/-- An étale surjection induces an epimorphism of original represented sheaves. -/
theorem representedSheafMap_epi_of_etale_surjective
    {X : Scheme.{u}} {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (p : H ⟶ K) [Etale p.hom.hom.left] [Surjective p.hom.hom.left] :
    Epi (representedSheafMap p) := by
  apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} _).mp
  constructor
  intro U a
  let t : (Scheme.Etale.forget X).obj U ⟶ K.X := a.down.toMul
  let f := p.hom.hom.left
  let g : pullback f t.left ⟶ U.left := pullback.snd f t.left
  let : MorphismProperty.IsStableUnderBaseChange (@Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange
  let : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u}) :=
    Surjective.instIsStableUnderBaseChangeScheme
  let : Etale g := MorphismProperty.of_isPullback (P := @Etale)
    (IsPullback.of_hasPullback f t.left) (inferInstance : Etale p.hom.hom.left)
  let hg : Surjective g := MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback f t.left) (inferInstance : Surjective p.hom.hom.left)
  let : Etale U.hom := U.prop
  let V : X.Etale := Scheme.Etale.mk (g ≫ U.hom)
  let q : V ⟶ U := MorphismProperty.Over.homMk g rfl
  let s : (Scheme.Etale.forget X).obj V ⟶ H.X :=
    Over.homMk (pullback.fst f t.left) (by
      change pullback.fst f t.left ≫ H.X.hom = g ≫ U.hom
      calc
        _ = (pullback.fst f t.left ≫ f) ≫ K.X.hom := by
          rw [Category.assoc, Over.w p.hom.hom]
        _ = (g ≫ t.left) ≫ K.X.hom :=
          congrArg (fun (v : pullback f t.left ⟶ K.X.left) => v ≫ K.X.hom)
            (pullback.condition (f := f) (g := t.left))
        _ = _ := (Category.assoc _ _ _).trans
          (congrArg (fun (v : U.left ⟶ X) => g ≫ v) (Over.w t)))
  have hc : Sieve.ofArrows (fun _ : PUnit.{1} => V) (fun _ => q) ∈
      X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ _ : PUnit.{1}, Set.range g) = Set.univ
    simp only [Set.iUnion_const]
    exact Set.range_eq_univ.mpr hg.surj
  apply X.smallEtaleTopology.superset_covering ?_ hc
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro _
  refine ⟨ULift.up (Additive.ofMul s), ?_⟩
  apply ULift.ext
  change Additive.ofMul (s ≫ p.hom.hom) = Additive.ofMul ((Scheme.Etale.forget X).map q ≫ t)
  apply congrArg Additive.ofMul
  ext : 1
  exact pullback.condition

end AlgebraicGeometry.Scheme.EtaleCohomology
