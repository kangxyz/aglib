/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.LineBundle
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedComposition
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# An original projective embedding with symmetric pulled O(1)

Choose the existing finite-coordinate closed embedding once. Its composite
with the original inversion is the graph map used in the existing closed
Segre composition. The proved Segre line-bundle comparison identifies the
new pulled O(1) with the tensor of the two original pullbacks. Inversion
exchanges their classes.

This is an existence theorem on the same group scheme, with no supplied
polarization law, alternative group model or commutativity assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

/-- Projectivity supplies a closed embedding of the original field group
whose original pulled-back O(1) class is symmetric under the original inversion. -/
theorem exists_symmetric_projective_embedding {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsHProjective G.hom] :
    ∃ (I : Type u) (_ : Finite I) (j : G.left ⟶ ProjectiveSpace k I),
      IsClosedImmersion j ∧ j ≫ ProjectiveSpace.toSpec k I = G.hom ∧
        pullbackClass ((𝟙 G)⁻¹).left
          (pullbackClass j (classOf _ (ProjectiveSpace.twistingLineBundle k I 1))) =
        pullbackClass j (classOf _ (ProjectiveSpace.twistingLineBundle k I 1)) := by
  obtain ⟨I, hI, i, hi, hp⟩ := IsHProjective.exists_isClosedImmersion (f := G.hom)
  let : Finite I := hI
  let : IsClosedImmersion i := hi
  let v : G ⟶ G := (𝟙 G)⁻¹
  have hv : v ≫ v = 𝟙 G := by
    simp only [v, GrpObj.comp_inv, Category.comp_id, inv_inv]
  have hgraph : (𝟙 G.left) ≫ G.hom =
      (v.left ≫ i) ≫ ProjectiveSpace.toSpec k I := by
    rw [Category.id_comp, Category.assoc, hp]
    exact (Over.w v).symm
  let h : G.left ⟶ pullback G.hom (ProjectiveSpace.toSpec k I) :=
    pullback.lift (𝟙 _) (v.left ≫ i) hgraph
  have hh : h ≫ pullback.fst G.hom (ProjectiveSpace.toSpec k I) = 𝟙 G.left := by
    simp only [h, pullback.lift_fst]
  let : IsClosedImmersion (h ≫ pullback.fst G.hom (ProjectiveSpace.toSpec k I)) := by
    rw [hh]
    infer_instance
  let : IsClosedImmersion h :=
    IsClosedImmersion.of_comp h (pullback.fst G.hom (ProjectiveSpace.toSpec k I))
  let j := ProjectiveSpace.Segre.closedCompositionMap k I I G.hom i hp h
  let a := h ≫ ProjectiveSpace.Segre.baseEmbeddingProductMap k I I G.hom i hp
  have hj : j = a ≫ ProjectiveSpace.Segre.embedding k I I := by
    simp only [j, a, ProjectiveSpace.Segre.closedCompositionMap, Category.assoc]
  have ha₁ : a ≫ ProjectiveSpace.Segre.first k I I = v.left ≫ i := by
    simp only [a, Category.assoc, ProjectiveSpace.Segre.baseEmbeddingProductMap_first,
      h, pullback.lift_snd]
  have ha₂ : a ≫ ProjectiveSpace.Segre.second k I I = i := by
    dsimp only [a]
    rw [Category.assoc, ProjectiveSpace.Segre.baseEmbeddingProductMap_second,
      ← Category.assoc, hh, Category.id_comp]
  let A := pullbackClass i (classOf _ (ProjectiveSpace.twistingLineBundle k I 1))
  have hc : pullbackClass j (classOf _ (ProjectiveSpace.twistingLineBundle k (I × I) 1)) =
      pullbackClass v.left A + A := by
    rw [hj]
    have hclass := ProjectiveSpace.Segre.pullbackClass_twisting_one_comp
      (ProjectiveSpace.Segre.first k I I) (ProjectiveSpace.Segre.second k I I) a
    change pullbackClass (a ≫ ProjectiveSpace.Segre.embedding k I I)
      (classOf _ (ProjectiveSpace.twistingLineBundle k (I × I) 1)) = _ at hclass
    rw [ha₁, ha₂, pullbackClass_comp v.left i] at hclass
    exact hclass
  have hinv : pullbackClass v.left (pullbackClass v.left A) = A := by
    rw [← pullbackClass_comp, ← Over.comp_left, hv, Over.id_left, pullbackClass_id]
  refine ⟨I × I, inferInstance, j, inferInstance, ?_, ?_⟩
  · change ProjectiveSpace.Segre.closedCompositionMap k I I G.hom i hp h ≫ _ = _
    rw [ProjectiveSpace.Segre.closedCompositionMap_toSpec, ← Category.assoc, hh,
      Category.id_comp]
  · change pullbackClass v.left _ = _
    rw [hc, pullbackClass_add, hinv, add_comm]

end AlgebraicGeometry.Scheme.Group.Multiplication
