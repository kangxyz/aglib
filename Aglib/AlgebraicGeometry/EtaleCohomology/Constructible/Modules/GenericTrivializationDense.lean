/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.DenseEtaleOpen

/-! # Actual finite etale module trivializations on a dense open

For a finite-type locally constant native module sheaf on an integral scheme,
choose its actual chart over the generic point and restrict that chart to an
affine open. Generic finiteness and density give a finite etale surjective cover
after shrinking the base. The original chart's finitely generated module value
and module-valued constant isomorphism are transported through the original
inverse-image composition. No finiteness of the underlying group is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- An actual dense affine open and a finite etale surjective cover on which
the original native module coefficient becomes constant. -/
structure DenseFiniteEtaleTrivialization {X : Scheme.{u}} (F : ModuleSheaf R X) where
  /-- The actual affine open base. -/
  base : Scheme.{u}
  /-- Its original inclusion into the original base scheme. -/
  inclusion : base ⟶ X
  /-- The base is affine. -/
  affine_base : IsAffine base
  /-- The original inclusion is an open immersion. -/
  open_inclusion : IsOpenImmersion inclusion
  /-- The open base is nonempty. -/
  nonempty_base : Nonempty base
  /-- The original inclusion has dense image. -/
  dense_inclusion : IsDominant inclusion
  /-- The actual trivializing cover. -/
  cover : Scheme.{u}
  /-- The actual cover projection. -/
  projection : cover ⟶ base
  /-- The actual projection is finite. -/
  finite_projection : IsFinite projection
  /-- The actual projection is etale. -/
  etale_projection : Etale projection
  /-- The actual projection is surjective. -/
  surjective_projection : Surjective projection
  /-- The original module value, with its original universe. -/
  value : ModuleCat.{u + 1} R
  /-- Finite generation over the original coefficient ring. -/
  finite_value : Module.Finite R value
  /-- The original module inverse image is genuinely constant. -/
  iso : (moduleInverseImage R (projection ≫ inclusion)).obj F ≅
    (constantSheaf cover.smallEtaleTopology (ModuleCat.{u + 1} R)).obj value

/-- An affine integral base has an actual dense finite etale module
trivialization obtained from its original generic-point chart. -/
def denseFiniteEtaleTrivializationOfIsAffine {X : Scheme.{u}}
    [IsAffine X] [IsIntegral X] (F : ModuleSheaf R X)
    (hF : IsFiniteTypeLocallyConstant F) : DenseFiniteEtaleTrivialization F := by
  apply Classical.choice
  obtain ⟨t⟩ := hF
  obtain ⟨i, y, _⟩ := t.covers (genericPoint X)
  have : Etale (t.chart i).hom := (t.chart i).prop
  obtain ⟨A, b, hb, ⟨z, _⟩, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := y) (U := ⊤) (by simp)
  have : IsOpenImmersion b := hb
  have : Nonempty (Spec A) := ⟨z⟩
  let p : Spec A ⟶ X := b ≫ (t.chart i).hom
  have hconst : (moduleInverseImage R p).obj F ≅
      (constantSheaf (Spec A).smallEtaleTopology (ModuleCat.{u + 1} R)).obj (t.value i) :=
    (moduleInverseImageComp R (t.chart i).hom b).app F ≪≫
      (moduleInverseImage R b).mapIso (t.trivialization i) ≪≫
      (moduleInverseImageConstantIso R b).app (t.value i)
  obtain ⟨S, j, hSaff, hj, hSne, hjdense, hfinite, hetale, hsurj⟩ :=
    exists_dense_finiteEtale_open_of_isAffineHom (X := X) p
  let q := pullback.snd p j
  let a := pullback.fst p j
  have square : q ≫ j = a ≫ p := pullback.condition.symm
  refine ⟨{ base := S
            inclusion := j
            affine_base := hSaff
            open_inclusion := hj
            nonempty_base := hSne
            dense_inclusion := hjdense
            cover := pullback p j
            projection := q
            finite_projection := hfinite
            etale_projection := hetale
            surjective_projection := hsurj
            value := t.value i
            finite_value := t.finite_value i
            iso := ?_ }⟩
  exact eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F) square) ≪≫
    (moduleInverseImageComp R p a).app F ≪≫
      (moduleInverseImage R a).mapIso hconst ≪≫
      (moduleInverseImageConstantIso R a).app (t.value i)

/-- A finite-type locally constant native module sheaf on any integral scheme
has an actual finite etale constant trivialization over a dense affine open.
There is no Noetherian or finite-underlying-group hypothesis. -/
def denseFiniteEtaleTrivialization {X : Scheme.{u}} [IsIntegral X]
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) :
    DenseFiniteEtaleTrivialization F := by
  apply Classical.choice
  obtain ⟨A, a, ha, ⟨z, _⟩, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := genericPoint X) (U := ⊤) (by simp)
  have : IsOpenImmersion a := ha
  have : Nonempty (Spec A) := ⟨z⟩
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion a
  have : IsDominant a := ⟨a.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let t := denseFiniteEtaleTrivializationOfIsAffine ((moduleInverseImage R a).obj F)
    (isFiniteTypeLocallyConstant_pullback a hF)
  have : IsOpenImmersion t.inclusion := t.open_inclusion
  have : IsDominant t.inclusion := t.dense_inclusion
  refine ⟨{ base := t.base
            inclusion := t.inclusion ≫ a
            affine_base := t.affine_base
            open_inclusion := inferInstance
            nonempty_base := t.nonempty_base
            dense_inclusion := inferInstance
            cover := t.cover
            projection := t.projection
            finite_projection := t.finite_projection
            etale_projection := t.etale_projection
            surjective_projection := t.surjective_projection
            value := t.value
            finite_value := t.finite_value
            iso := ?_ }⟩
  exact eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F)
      (Category.assoc t.projection t.inclusion a).symm) ≪≫
    (moduleInverseImageComp R a (t.projection ≫ t.inclusion)).app F ≪≫ t.iso

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
