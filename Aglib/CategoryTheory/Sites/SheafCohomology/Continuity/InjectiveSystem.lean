/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Product envelopes for systems in varying categories

This is the product construction underlying Stacks Project, Tag 0EXZ.
Transitions are oriented by adjunction as `F i ⟶ R(a)(F j)`. Actual right
adjoints and their original identity/composition comparisons are retained.
The envelope transitions and the embedding are constructed from product
projections, not supplied as assumptions. Their system coherence is a separate
step, requiring the original comparison isomorphisms' coherence laws.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem

universe vI vA uI uA

variable {I : Type uI} [Category.{vI} I]
  (A : I → Type uA) [∀ i, Category.{vA} (A i)]

/-- Actual adjunctions and comparison isomorphisms for the varying categories.
No identity or composition of functors is required to hold definitionally. -/
structure AdjunctionData where
  /-- The left adjoint associated to an indexing arrow. -/
  left : ∀ {i j : I}, (i ⟶ j) → A i ⥤ A j
  /-- The right adjoint associated to an indexing arrow. -/
  right : ∀ {i j : I}, (i ⟶ j) → A j ⥤ A i
  /-- The specified adjunction for each indexing arrow. -/
  adj : ∀ {i j : I} (a : i ⟶ j), left a ⊣ right a
  left_preservesMonomorphisms : ∀ {i j : I} (a : i ⟶ j),
    (left a).PreservesMonomorphisms
  /-- The right-adjoint comparison for an identity arrow. -/
  idIso : ∀ i, right (𝟙 i) ≅ 𝟭 (A i)
  /-- The right-adjoint comparison for a composite of indexing arrows. -/
  compIso : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
    right (a ≫ b) ≅ right b ⋙ right a

attribute [instance] AdjunctionData.left_preservesMonomorphisms

variable {A} (D : AdjunctionData A)

/-- A coefficient system expressed using the original right adjoints. -/
structure System where
  /-- The coefficient object in the category at each index. -/
  obj : ∀ i, A i
  /-- The transition to the right-adjoint image of the target coefficient. -/
  map : ∀ {i j : I} (a : i ⟶ j), obj i ⟶ (D.right a).obj (obj j)
  map_id : ∀ i, map (𝟙 i) ≫ (D.idIso i).hom.app (obj i) = 𝟙 (obj i)
  map_comp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
    map (a ≫ b) ≫ (D.compIso a b).hom.app (obj k) =
      map a ≫ (D.right a).map (map b)

/-- All arrows leaving an index, with their targets retained. -/
abbrev Outgoing (i : I) := Σ j : I, i ⟶ j

variable [∀ i, EnoughInjectives (A i)]
  [∀ i j : I, HasProductsOfShape (Outgoing j) (A i)]

/-- The injective factor belonging to an outgoing arrow. -/
abbrev factor (F : System D) (i : I) (b : Outgoing i) : A i :=
  (D.right b.2).obj (Injective.under (F.obj b.1))

instance factor_injective (F : System D) (i : I) (b : Outgoing i) :
    Injective (factor D F i b) :=
  Injective.injective_of_adjoint (D.adj b.2) _

/-- The product envelope at one index. -/
abbrev envelope (F : System D) (i : I) : A i := ∏ᶜ factor D F i

instance envelope_injective (F : System D) (i : I) : Injective (envelope D F i) := by
  unfold envelope
  infer_instance

/-- The actual embedding into the product envelope. -/
def embedding (F : System D) (i : I) : F.obj i ⟶ envelope D F i :=
  Pi.lift fun b => F.map b.2 ≫ (D.right b.2).map (Injective.ι (F.obj b.1))

@[reassoc (attr := simp)]
theorem embedding_π (F : System D) (i : I) (b : Outgoing i) :
    embedding D F i ≫ Pi.π (factor D F i) b =
      F.map b.2 ≫ (D.right b.2).map (Injective.ι (F.obj b.1)) :=
  Pi.lift_comp_π _ _

/-- The identity-arrow projection recovers the chosen injective embedding. -/
@[reassoc]
theorem embedding_identity (F : System D) (i : I) :
    embedding D F i ≫ Pi.π (factor D F i) ⟨i, 𝟙 i⟩ ≫
      (D.idIso i).hom.app (Injective.under (F.obj i)) = Injective.ι (F.obj i) := by
  rw [← Category.assoc, embedding_π, Category.assoc,
    (D.idIso i).hom.naturality, ← Category.assoc, F.map_id]
  exact Category.id_comp _

instance embedding_mono (F : System D) (i : I) : Mono (embedding D F i) :=
  mono_of_mono_fac (embedding_identity D F i)

instance right_isRightAdjoint {i j : I} (a : i ⟶ j) :
    (D.right a).IsRightAdjoint :=
  ⟨D.left a, ⟨D.adj a⟩⟩

/-- The envelope transition is induced by composition of outgoing arrows and
the original right-adjoint composition comparison. -/
def transition (F : System D) {i j : I} (a : i ⟶ j) :
    envelope D F i ⟶ (D.right a).obj (envelope D F j) :=
  (Pi.lift fun b : Outgoing j =>
    Pi.π (factor D F i) ⟨b.1, a ≫ b.2⟩ ≫
      (D.compIso a b.2).hom.app (Injective.under (F.obj b.1))) ≫
    inv (piComparison (D.right a) (factor D F j))

/-- Every original direct-image projection of the transition has the expected
composite-arrow formula. -/
@[reassoc]
theorem transition_π (F : System D) {i j : I} (a : i ⟶ j) (b : Outgoing j) :
    transition D F a ≫ (D.right a).map (Pi.π (factor D F j) b) =
      Pi.π (factor D F i) ⟨b.1, a ≫ b.2⟩ ≫
        (D.compIso a b.2).hom.app (Injective.under (F.obj b.1)) := by
  unfold transition
  rw [Category.assoc, inv_piComparison_comp_map_π]
  exact Pi.lift_comp_π
    (fun c : Outgoing j => Pi.π (factor D F i) ⟨c.1, a ≫ c.2⟩ ≫
      (D.compIso a c.2).hom.app (Injective.under (F.obj c.1))) b

/-- The component embeddings commute with the actual envelope transitions. -/
@[reassoc]
theorem embedding_transition (F : System D) {i j : I} (a : i ⟶ j) :
    embedding D F i ≫ transition D F a =
      F.map a ≫ (D.right a).map (embedding D F j) := by
  apply (cancel_mono (piComparison (D.right a) (factor D F j))).1
  apply Pi.hom_ext
  intro b
  simp only [Category.assoc, piComparison_comp_π]
  rw [transition_π, embedding_π_assoc]
  rw [← Functor.map_comp, embedding_π, Functor.map_comp]
  rw [(D.compIso a b.2).hom.naturality]
  change F.map (a ≫ b.2) ≫ (D.compIso a b.2).hom.app (F.obj b.1) ≫
      (D.right a).map ((D.right b.2).map (Injective.ι (F.obj b.1))) = _
  rw [← Category.assoc, F.map_comp, Category.assoc]

end CategoryTheory.InjectiveSystem
