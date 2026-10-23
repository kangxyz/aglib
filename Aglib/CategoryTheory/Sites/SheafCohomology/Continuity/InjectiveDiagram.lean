/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Compatible embeddings into objectwise injective diagrams

For a diagram `F`, take at `i` the product, over all arrows `i ⟶ j`,
of chosen injective objects under `F.obj j`. Reindexing the projections gives
an actual functor, without making the individual choices of injective objects
functorial. The identity-arrow projection proves that its natural embedding is
objectwise monic. This is the fixed-site case of Stacks Project, Tag 0EXZ.

Object and morphism index universes are independent. Only products indexed by
the objects and by the individual hom types of the index category are required.
No filteredness, abelian structure, or injectivity in the diagram category is
assumed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Functor.InjectiveDiagram

universe vI vA uI uA

variable {I : Type uI} [Category.{vI} I]
  {A : Type uA} [Category.{vA} A]
  [EnoughInjectives A] [HasProductsOfShape I A]
  [∀ i j : I, HasProductsOfShape (i ⟶ j) A]

/-- An objectwise injective replacement of a diagram, with transition maps
obtained by reindexing arrow projections. -/
def replacement (F : I ⥤ A) : I ⥤ A where
  obj i := ∏ᶜ fun j : I => ∏ᶜ fun _ : i ⟶ j => Injective.under (F.obj j)
  map f := Pi.lift fun j => Pi.lift fun g => Pi.π _ j ≫ Pi.π _ (f ≫ g)
  map_id i := by
    apply Pi.hom_ext
    intro j
    apply Pi.hom_ext
    intro g
    simp
  map_comp f g := by
    apply Pi.hom_ext
    intro j
    apply Pi.hom_ext
    intro h
    simp [Category.assoc]

/-- Each replacement component is a product of injective objects. -/
instance replacement_obj_injective (F : I ⥤ A) (i : I) :
    Injective ((replacement F).obj i) := by
  change Injective (∏ᶜ fun j : I => ∏ᶜ fun _ : i ⟶ j => Injective.under (F.obj j))
  infer_instance

/-- The compatible embedding, whose arrow-indexed components are the original
transition maps followed by the chosen injective embeddings. -/
def ι (F : I ⥤ A) : F ⟶ replacement F where
  app i := Pi.lift fun j => Pi.lift fun f => F.map f ≫ Injective.ι (F.obj j)
  naturality i j f := by
    apply Pi.hom_ext
    intro k
    apply Pi.hom_ext
    intro g
    simp [replacement, Functor.map_comp, Category.assoc]

/-- The formula for the actual embedding on every arrow projection. -/
@[reassoc (attr := simp)]
theorem ι_app_π (F : I ⥤ A) {i j : I} (f : i ⟶ j) :
    (ι F).app i ≫ Pi.π _ j ≫ Pi.π _ f = F.map f ≫ Injective.ι (F.obj j) := by
  change (Pi.lift fun k : I => Pi.lift fun g : i ⟶ k =>
      F.map g ≫ Injective.ι (F.obj k)) ≫
    Pi.π (fun k : I => ∏ᶜ fun _ : i ⟶ k => Injective.under (F.obj k)) j ≫
      Pi.π (fun _ : i ⟶ j => Injective.under (F.obj j)) f = _
  exact (Pi.lift_comp_π_assoc
    (fun k : I => Pi.lift fun g : i ⟶ k => F.map g ≫ Injective.ι (F.obj k)) j
    (Pi.π (fun _ : i ⟶ j => Injective.under (F.obj j)) f)).trans
      (Pi.lift_comp_π (fun g : i ⟶ j => F.map g ≫ Injective.ι (F.obj j)) f)

/-- The identity-arrow projection recovers the original chosen monomorphism. -/
@[reassoc]
theorem ι_app_identity (F : I ⥤ A) (i : I) :
    (ι F).app i ≫ Pi.π _ i ≫ Pi.π _ (𝟙 i) = Injective.ι (F.obj i) := by
  simp

/-- Every component of the compatible embedding is monic. -/
instance ι_app_mono (F : I ⥤ A) (i : I) : Mono ((ι F).app i) :=
  mono_of_mono_fac (ι_app_identity F i)

/-- The embedding is a monomorphism in the actual functor category. -/
instance ι_mono (F : I ⥤ A) : Mono (ι F) :=
  NatTrans.mono_of_mono_app (ι F)

/-- Every diagram admits a compatible monomorphism into an objectwise
injective diagram, without a functorial choice of injective presentations. -/
theorem exists_objectwise_injective_embedding (F : I ⥤ A) :
    ∃ (Q : I ⥤ A) (η : F ⟶ Q), Mono η ∧
      (∀ i, Mono (η.app i)) ∧ (∀ i, Injective (Q.obj i)) :=
  ⟨replacement F, ι F, inferInstance, fun _ => inferInstance, fun _ => inferInstance⟩

end CategoryTheory.Functor.InjectiveDiagram
