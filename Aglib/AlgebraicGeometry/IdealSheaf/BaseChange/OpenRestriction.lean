/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion

/-!
# Ideal modules restricted to open subschemes

The original cartesian ideal map gives the ideal of a factored morphism. The ideal of an
empty source is the structure module through its original kernel inclusion. Consequently an
ideal restricts to the structure module on an open disjoint from its image. No closed-immersion
hypothesis is required. The first two constructions were formerly in the Weierstrass family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Pulling the ideal of a factored morphism back through an open immersion
recovers its actual factor ideal. -/
def idealModulePullbackFactor {D U X : Scheme.{u}} (p : D ⟶ U)
    (i : U ⟶ X) [IsOpenImmersion i] :
    (Scheme.Modules.pullback i).obj (idealModule (p ≫ i)) ≅ idealModule p := by
  have h : (𝟙 D) ≫ (p ≫ i) = p ≫ i := Category.id_comp _
  have H : IsPullback (𝟙 D) p (p ≫ i) i :=
    IsPullback.of_horiz_isIso_mono ⟨h⟩
  have : IsIso (idealPullbackMap (p ≫ i) p i (𝟙 D) h) :=
    idealPullbackMap_isIso_of_isOpenImmersion (p ≫ i) p i (𝟙 D) h H
  exact asIso (idealPullbackMap (p ≫ i) p i (𝟙 D) h)

/-- The factor isomorphism uses the original ideal comparison map. -/
@[simp] theorem idealModulePullbackFactor_hom {D U X : Scheme.{u}} (p : D ⟶ U)
    (i : U ⟶ X) [IsOpenImmersion i] :
    (idealModulePullbackFactor p i).hom =
      idealPullbackMap (p ≫ i) p i (𝟙 D) (Category.id_comp _) := rfl

/-- The ideal of a morphism from an empty scheme is the unit module. -/
def idealModuleEmptyIso {D X : Scheme.{u}} [IsEmpty D] (i : D ⟶ X) :
    idealModule i ≅ SheafOfModules.unit X.ringCatSheaf := by
  have hz : structureModuleMap i = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    have hU : i ⁻¹ᵁ U = ⊥ := SetLike.ext fun x => isEmptyElim x
    let : Subsingleton Γ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit D.ringCatSheaf), U) := by
      change Subsingleton Γ(D, i ⁻¹ᵁ U)
      rw [hU]
      infer_instance
    ext a
    exact Subsingleton.elim _ _
  exact kernelIsoOfEq hz ≪≫ kernelZeroIsoSource

/-- The empty-source isomorphism is the original ideal inclusion. -/
@[simp] theorem idealModuleEmptyIso_hom {D X : Scheme.{u}} [IsEmpty D] (i : D ⟶ X) :
    (idealModuleEmptyIso i).hom = idealInclusion i := by
  exact kernelIsoOfEq_hom_comp_ι _

/-- Disjoint images give an empty actual fibre product. -/
theorem isEmpty_pullback_of_disjoint_ranges {D U X : Scheme.{u}} (i : D ⟶ X) (j : U ⟶ X)
    (h : Disjoint (Set.range i) (Set.range j)) : IsEmpty (pullback (C := Scheme.{u}) i j) := by
  constructor
  intro z
  have hc := congrArg (fun f : pullback i j ⟶ X => f z)
    (pullback.condition (f := i) (g := j))
  exact Set.disjoint_left.mp h ⟨pullback.fst i j z, rfl⟩ ⟨pullback.snd i j z, hc.symm⟩

/-- An ideal restricts to the structure module on a disjoint open subscheme. -/
def idealModulePullbackIsoOfDisjoint {D U X : Scheme.{u}} (i : D ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (h : Disjoint (Set.range i) (Set.range j)) :
    (Scheme.Modules.pullback j).obj (idealModule i) ≅ SheafOfModules.unit U.ringCatSheaf :=
  haveI := isEmpty_pullback_of_disjoint_ranges i j h
  haveI := idealPullbackMap_isIso_of_isOpenImmersion i (pullback.snd i j) j
    (pullback.fst i j) pullback.condition (IsPullback.of_hasPullback i j)
  asIso (idealPullbackMap i (pullback.snd i j) j (pullback.fst i j) pullback.condition) ≪≫
    idealModuleEmptyIso (pullback.snd i j)

/-- The disjoint-open comparison factors through the original cartesian ideal map. -/
theorem idealModulePullbackIsoOfDisjoint_hom {D U X : Scheme.{u}} (i : D ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] (h : Disjoint (Set.range i) (Set.range j)) :
    (idealModulePullbackIsoOfDisjoint i j h).hom =
      idealPullbackMap i (pullback.snd i j) j (pullback.fst i j) pullback.condition ≫
        idealInclusion (pullback.snd i j) := by
  have := isEmpty_pullback_of_disjoint_ranges i j h
  change _ ≫ (idealModuleEmptyIso (pullback.snd i j)).hom = _
  rw [idealModuleEmptyIso_hom]
  rfl

end AlgebraicGeometry.Scheme.Hom
