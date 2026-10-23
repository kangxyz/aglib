/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveSystem

/-! # Coherent injective replacements for varying coefficient systems

The hypotheses concern the original identity and composition comparisons of
right adjoints. The replacement's transition identities and composition laws
are proved from those hypotheses by their actual product projections.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem

universe vI vA uI uA

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  (D : AdjunctionData A)

/-- The original right-adjoint comparisons obey their unit and associativity
laws, including equality transport in the indexing category. -/
structure AdjunctionData.Coherent : Prop where
  id_comp : ∀ {i j : I} (a : i ⟶ j) (X : A j),
    (D.compIso (𝟙 i) a).hom.app X ≫ (D.idIso i).hom.app ((D.right a).obj X) =
      eqToHom (congrArg (fun b => (D.right b).obj X) (Category.id_comp a))
  comp_id : ∀ {i j : I} (a : i ⟶ j) (X : A j),
    (D.compIso a (𝟙 j)).hom.app X ≫ (D.right a).map ((D.idIso j).hom.app X) =
      eqToHom (congrArg (fun b => (D.right b).obj X) (Category.comp_id a))
  assoc : ∀ {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) (X : A l),
    (D.compIso (a ≫ b) c).hom.app X ≫
      (D.compIso a b).hom.app ((D.right c).obj X) =
    eqToHom (congrArg (fun d => (D.right d).obj X) (Category.assoc a b c)) ≫
      (D.compIso a (b ≫ c)).hom.app X ≫
        (D.right a).map ((D.compIso b c).hom.app X)

variable [∀ i, EnoughInjectives (A i)]
  [∀ i j : I, HasProductsOfShape (Outgoing j) (A i)]

private theorem projection_transport (F : System D) {i j : I}
    (a b : i ⟶ j) (h : a = b) :
    Pi.π (factor D F i) ⟨j, a⟩ ≫
      eqToHom (congrArg (fun c => (D.right c).obj (Injective.under (F.obj j))) h) =
      Pi.π (factor D F i) ⟨j, b⟩ := by
  subst b
  simp

/-- The envelope transitions satisfy the original identity comparison. -/
theorem transition_id (hD : D.Coherent) (F : System D) (i : I) :
    transition D F (𝟙 i) ≫ (D.idIso i).hom.app (envelope D F i) =
      𝟙 (envelope D F i) := by
  apply Pi.hom_ext
  intro b
  rw [Category.assoc]
  change transition D F (𝟙 i) ≫
      ((D.idIso i).hom.app (envelope D F i) ≫
        (𝟭 (A i)).map (Pi.π (factor D F i) b)) = _
  rw [← (D.idIso i).hom.naturality, ← Category.assoc, transition_π, Category.assoc,
    hD.id_comp]
  exact (projection_transport D F _ _ (Category.id_comp b.2)).trans
    (Category.id_comp _).symm

/-- The envelope transitions satisfy the original composition comparison. -/
theorem transition_comp (hD : D.Coherent) (F : System D)
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    transition D F (a ≫ b) ≫ (D.compIso a b).hom.app (envelope D F k) =
      transition D F a ≫ (D.right a).map (transition D F b) := by
  apply (cancel_mono (piComparison (D.right b ⋙ D.right a) (factor D F k))).1
  apply Pi.hom_ext
  intro c
  simp only [Category.assoc, piComparison_comp_π]
  rw [← (D.compIso a b).hom.naturality]
  rw [← Category.assoc, transition_π, Category.assoc, hD.assoc]
  rw [← Category.assoc, ← Category.assoc,
    projection_transport D F _ _ (Category.assoc a b c.2)]
  change (Pi.π (factor D F i) ⟨c.1, a ≫ (b ≫ c.2)⟩ ≫
      (D.compIso a (b ≫ c.2)).hom.app (Injective.under (F.obj c.1))) ≫
        (D.right a).map ((D.compIso b c.2).hom.app (Injective.under (F.obj c.1))) = _
  rw [← transition_π D F a ⟨c.1, b ≫ c.2⟩, Category.assoc, ← Functor.map_comp,
    ← transition_π D F b c]
  simp only [Functor.map_comp, Functor.comp_map]

/-- The actual objectwise injective replacement system. -/
def replacement (hD : D.Coherent) (F : System D) : System D where
  obj := envelope D F
  map := transition D F
  map_id := transition_id D hD F
  map_comp := transition_comp D hD F

/-- Morphisms of systems retain the original right-adjoint transition squares. -/
structure System.Hom (F G : System D) where
  /-- The morphism at each index of the coefficient systems. -/
  app : ∀ i, F.obj i ⟶ G.obj i
  naturality : ∀ {i j : I} (a : i ⟶ j),
    app i ≫ G.map a = F.map a ≫ (D.right a).map (app j)

/-- The actual compatible embedding into the constructed injective system. -/
def replacementEmbedding (hD : D.Coherent) (F : System D) :
    System.Hom D F (replacement D hD F) where
  app := embedding D F
  naturality := embedding_transition D F

instance replacement_obj_injective (hD : D.Coherent) (F : System D) (i : I) :
    Injective ((replacement D hD F).obj i) :=
  envelope_injective D F i

instance replacementEmbedding_mono (hD : D.Coherent) (F : System D) (i : I) :
    Mono ((replacementEmbedding D hD F).app i) :=
  embedding_mono D F i

/-- The varying-category product construction gives a compatible embedding
into an objectwise injective system. -/
theorem exists_injective_system (hD : D.Coherent) (F : System D) :
    ∃ (Q : System D) (η : System.Hom D F Q),
      (∀ i, Mono (η.app i)) ∧ (∀ i, Injective (Q.obj i)) :=
  ⟨replacement D hD F, replacementEmbedding D hD F,
    fun _ => inferInstance, fun _ => inferInstance⟩

end CategoryTheory.InjectiveSystem
