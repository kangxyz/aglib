/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.LocalFiniteComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.ConstantMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.FiniteConstants.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Aglib.AlgebraicGeometry.Spec.CompletionSpecialization

/-! # Finite covers of the line over a henselian coefficient algebra

Finite-pure comparison identifies the original total closed-residue restriction.
The local finite-cover comparison is injective, so it detects the equality
needed to lift any class from the actual coefficient algebra to the ground field.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.FieldComparison

universe u

attribute [local instance] hasSheafifyLarge

section CoefficientMaps

variable {k C D E : Type u} [CommRing k] [CommRing C] [CommRing D] [CommRing E]
  [Algebra k C] [Algebra k D] [Algebra k E]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))

/-- The original map between standard-order coefficient pullbacks. -/
def coefficientPullbackMap (a : C →ₐ[k] D) :
    pullback p (Spec.algebraMap k D) ⟶ pullback p (Spec.algebraMap k C) :=
  pullback.lift (pullback.fst p (Spec.algebraMap k D))
    (pullback.snd p (Spec.algebraMap k D) ≫ Spec.map (CommRingCat.ofHom a.toRingHom))
    (by
      rw [Category.assoc, LocalRing.specMap_algHom_triangle]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem coefficientPullbackMap_fst (a : C →ₐ[k] D) :
    coefficientPullbackMap p a ≫ pullback.fst p (Spec.algebraMap k C) =
      pullback.fst p (Spec.algebraMap k D) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem coefficientPullbackMap_snd (a : C →ₐ[k] D) :
    coefficientPullbackMap p a ≫ pullback.snd p (Spec.algebraMap k C) =
      pullback.snd p (Spec.algebraMap k D) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) :=
  pullback.lift_snd _ _ _

/-- The original coefficient-stage map respects composition of algebra maps. -/
theorem coefficientBaseChangeMap_comp (a : C →ₐ[k] D) (b : D →ₐ[k] E) :
    coefficientPullbackMap p b ≫ LocalRing.coefficientBaseChangeMap p a =
      LocalRing.coefficientBaseChangeMap p (b.comp a) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, LocalRing.coefficientBaseChangeMap_fst,
      coefficientPullbackMap_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  · simp only [Category.assoc, LocalRing.coefficientBaseChangeMap_snd,
      coefficientPullbackMap_fst]

end CoefficientMaps

section FiniteLineBaseChange

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 k)

/-- Base change of the finite cover, followed by the original line isomorphism. -/
def finiteBaseChangeLineOverMap :
    Over.mk (pullback.snd (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k R)) ⟶
      Over.mk (ProjectiveLine.structureMap R) :=
  (Over.pullback (Spec.algebraMap k R)).map
      (Over.homMk f rfl : Over.mk (f ≫ ProjectiveLine.structureMap k) ⟶
        Over.mk (ProjectiveLine.structureMap k)) ≫
    (AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineOverBaseChangeIso
      (algebraMap k R)).inv

/-- The finite map on the literal standard-order coefficient base change. -/
def finiteBaseChangeLineMap :
    pullback (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k R) ⟶
      ProjectiveLine.projectiveP1 R :=
  (finiteBaseChangeLineOverMap k R f).left

@[reassoc (attr := simp)]
theorem finiteBaseChangeLineMap_structureMap :
    finiteBaseChangeLineMap k R f ≫ ProjectiveLine.structureMap R =
      pullback.snd (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k R) :=
  (finiteBaseChangeLineOverMap k R f).w

instance [IsFinite f] : IsFinite (finiteBaseChangeLineMap k R f) := by
  let g : Over.mk (f ≫ ProjectiveLine.structureMap k) ⟶
      Over.mk (ProjectiveLine.structureMap k) := Over.homMk f rfl
  let hg : IsFinite (((Over.pullback (Spec.algebraMap k R)).map g).left) :=
    MorphismProperty.overPullbackMap (P := @IsFinite)
      (Spec.algebraMap k R) g (by change IsFinite f; infer_instance)
  let e := AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineOverBaseChangeIso
    (algebraMap k R)
  let : IsIso e.inv.left := inferInstanceAs
    (IsIso ((Over.forget (Spec (.of R))).map e.inv))
  change IsFinite (((Over.pullback (Spec.algebraMap k R)).map g).left ≫ e.inv.left)
  exact MorphismProperty.comp_mem (@IsFinite) _ _ hg inferInstance

end FiniteLineBaseChange

attribute [local instance] HasExt.standard

private theorem finiteLine_comparison_of_structure
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {Z : Scheme.{u}} (f : Z ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]
    (p : Z ⟶ Spec (.of R)) (hp : f ≫ ProjectiveLine.structureMap R = p)
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ) :
    Function.Bijective (Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p (LocalRing.residueSpecMap R)) q) := by
  subst p
  exact Curves.finite_projectiveLine_constantRestriction_bijective_of_isNoetherian f A q

variable (k R : Type u) [Field k] [CommRing R] [IsNoetherianRing R]
  [HenselianLocalRing R] [Algebra k R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  [Module.Finite k (IsLocalRing.ResidueField R)]
  [IsPurelyInseparable k (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 k) [IsFinite f]
  (A : Type u) [AddCommGroup A] [Finite A]

/-- The original constant restriction to a Noetherian henselian coefficient
algebra is bijective when its actual residue is finite purely inseparable.
Only schemes finite over the original projective line are covered. -/
theorem finite_projectiveLine_henselianField_constantRestriction_bijective (q : ℕ) :
    Function.Bijective (Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k R)) q) := by
  let p := f ≫ ProjectiveLine.structureMap k
  let κ := IsLocalRing.ResidueField R
  let g := pullback.fst p (Spec.algebraMap k R)
  let pR := pullback.snd p (Spec.algebraMap k R)
  let r := pullback.fst pR (LocalRing.residueSpecMap R)
  let gκ := pullback.fst p (Spec.algebraMap k κ)
  have hspec : LocalRing.residueSpecMap R ≫ Spec.algebraMap k R =
      (Iso.refl (Spec (.of κ))).hom ≫ Spec.algebraMap k κ := by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let e := LocalRing.residueFiberBaseChangeIso p (Spec.algebraMap k R)
    (Spec.algebraMap k κ) (LocalRing.residueSpecMap R) (Iso.refl _) hspec
  have he : e.hom ≫ gκ = r ≫ g :=
    LocalRing.residueFiberBaseChangeIso_hom_fst _ _ _ _ _ _
  have hpure : Function.Bijective (Curves.constantRestriction A gκ q) :=
    finitePure_constantCohomologyPullback_bijective k κ p A q
  have hiso : Function.Bijective (Curves.constantRestriction A e.hom q) :=
    (cohomologyMapIso_bijective ((inverseImageConstantIso e.hom).app (value A)) q).comp
      (cohomologyPullback_bijective_of_isEquivalence e.hom
        (coefficient A (pullback p (Spec.algebraMap k κ))) q)
  have heq (a : Sheaf.H.{u + 2} (coefficient A Y) q) :
      Curves.constantRestriction A e.hom q (Curves.constantRestriction A gκ q a) =
        Curves.constantRestriction A (r ≫ g) q a := by
    rw [← Curves.constantRestriction_comp, he]
  have ht : Function.Bijective (Curves.constantRestriction A (r ≫ g) q) := by
    constructor
    · intro a b hab
      apply hpure.injective
      apply hiso.injective
      rw [heq, heq, hab]
    · intro b
      obtain ⟨z, hz⟩ := hiso.surjective b
      obtain ⟨a, ha⟩ := hpure.surjective z
      refine ⟨a, ?_⟩
      rw [← heq, ha, hz]
  have hr : Function.Bijective (Curves.constantRestriction A r q) := by
    exact finiteLine_comparison_of_structure (finiteBaseChangeLineMap k R f) pR
      (finiteBaseChangeLineMap_structureMap k R f) A q
  constructor
  · intro a b hab
    apply ht.injective
    rw [Curves.constantRestriction_comp A g r, Curves.constantRestriction_comp A g r, hab]
  · intro b
    obtain ⟨a, ha⟩ := ht.surjective (Curves.constantRestriction A r q b)
    refine ⟨a, hr.injective ?_⟩
    rw [← Curves.constantRestriction_comp A g r, ha]

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.FieldComparison
