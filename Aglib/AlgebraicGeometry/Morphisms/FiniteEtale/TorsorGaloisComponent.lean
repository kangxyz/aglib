/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.RegularActionComponent
public import Aglib.CategoryTheory.TorsorAction.GlobalAction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFiber

/-! # Actual pointed Galois components of constant-group torsors

Global coefficient sections are evaluated on the original geometric point.
The literal trivial-cover labels prove surjectivity and connected-cover
morphism detection proves injectivity. The original torsor action therefore
has a regular fibre orbit, so its actual connected component is Galois. Its
deck group injects into the original global-section group and its order divides
the original finite label cardinality. No coefficient group law is placed on
the label type, and no cohomology model is imported here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.FiniteEtale.TorsorGaloisComponent

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
  (H : Grp (Over X)) {A : Type u} [Finite A]
  (e : H.X ≅ (trivialCover X A).obj)

include e in
/-- Evaluation of the original terminal coefficient sections is bijective;
no group structure or marking on the finite labels is assumed. -/
theorem sectionEvaluation_bijective :
    Function.Bijective (fun a : 𝟙_ (Over X) ⟶ H.X => toUnit (Over.mk s) ≫ a) := by
  constructor
  · intro a b hab
    let T := terminalCover X
    let : ConnectedSpace T.obj.left := inferInstanceAs (ConnectedSpace X)
    let : PreGaloisCategory.IsConnected T :=
      Connectedness.categoricalConnected_of_connectedSpace T
    have he : (ObjectProperty.homMk (a ≫ e.hom) : T ⟶ trivialCover X A) =
        ObjectProperty.homMk (b ≫ e.hom) := by
      apply PreGaloisCategory.evaluation_injective_of_isConnected
        (fiberToFinite s) T (trivialCover X A) (toUnit (Over.mk s))
      change (toUnit (Over.mk s) ≫ (a ≫ e.hom)) = toUnit (Over.mk s) ≫ (b ≫ e.hom)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ e.hom) hab).trans (Category.assoc _ _ _))
    exact (cancel_mono e.hom).mp (congrArg (fun f : T ⟶ trivialCover X A => f.hom) he)
  · intro b
    obtain ⟨a, ha⟩ := trivialCoverFiberPoint_surjective A s (b ≫ e.hom)
    refine ⟨(trivialCoverι X A a).hom ≫ e.inv, ?_⟩
    apply (cancel_mono e.hom).mp
    have hpoint : toUnit (Over.mk s) ≫ (trivialCoverι X A a).hom =
        trivialCoverFiberPoint A s a := by
      apply Over.OverMorphism.ext
      rfl
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hpoint.trans ha

include s e in
/-- The original section group has exactly the cardinality of the given
literal constant-cover labels. -/
theorem section_card : Nat.card (𝟙_ (Over X) ⟶ H.X) = Nat.card A := by
  let ev := Equiv.ofBijective _ (sectionEvaluation_bijective s H e)
  let post : (Over.mk s ⟶ H.X) ≃ Fiber s (trivialCover X A) :=
    { toFun := fun a => a ≫ e.hom
      invFun := fun a => a ≫ e.inv
      left_inv := fun a => by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      right_inv := fun a => by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] }
  exact Nat.card_congr (ev.trans (post.trans (trivialCoverFiberEquiv A s).symm))

variable (Y : Scheme.FiniteEtale X) (τ : TorsorAction H (toUnit Y.obj))

omit [ConnectedSpace X] in
/-- The actual terminal-section translations, lifted through the native full
subcategory without changing the underlying scheme maps. -/
def globalAction : (𝟙_ (Over X) ⟶ H.X) →* Aut Y where
  toFun a := ObjectProperty.isoMk (Scheme.finiteEtaleProperty X)
    (CategoryTheory.TorsorAction.globalAction τ a)
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact congrArg Iso.hom (CategoryTheory.TorsorAction.globalAction τ).map_one
  map_mul' a b := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact congrArg Iso.hom ((CategoryTheory.TorsorAction.globalAction τ).map_mul a b)

include e in
/-- The original fibre orbit is regular, derived from actual coefficient
section evaluation and the original torsor transport law. -/
theorem globalAction_orbit_bijective (y : Fiber s Y) :
    Function.Bijective (fun a => (fiberToFinite s).map (globalAction H Y τ a).hom y) := by
  exact CategoryTheory.TorsorAction.globalAction_orbit_bijective τ y
    (sectionEvaluation_bijective s H e)

include e in
/-- A specified original torsor fibre point lies on an actual connected
surjective Galois subcover. Its original deck maps are global translations,
and their group order divides the actual finite coefficient cardinality. -/
theorem exists_galois_component (y : Fiber s Y) :
    ∃ (Z : Scheme.FiniteEtale X) (i : Z ⟶ Y) (z : Fiber s Z),
      z ≫ i.hom = y ∧ Mono i ∧ PreGaloisCategory.IsGalois Z ∧
      ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom ∧
      ∃ δ : Aut Z →* (𝟙_ (Over X) ⟶ H.X), Function.Injective δ ∧
        (∀ σ, σ.hom ≫ i = i ≫ (globalAction H Y τ (δ σ)).hom) ∧
        Nat.card (Aut Z) ∣ Nat.card A := by
  obtain ⟨Z, i, z, hz, hi, hZ, δ, hδ, hover, hcard⟩ :=
    PreGaloisCategory.exists_galois_component_of_regularAction
      (fiberToFinite s) (globalAction H Y τ) y (globalAction_orbit_bijective s H e Y τ y)
  let := hZ
  let : ConnectedSpace Z.obj.left := Connectedness.connectedSpace_of_categoricalConnected Z
  have hsurj : Surjective Z.obj.hom := ⟨Set.range_eq_univ.mp
    ((structural_range_isClopen Z).eq_univ (Set.range_nonempty _))⟩
  refine ⟨Z, i, z, hz, hi, hZ, inferInstance, hsurj, δ, hδ, hover, ?_⟩
  exact (section_card s H e) ▸ hcard

end AlgebraicGeometry.Scheme.FiniteEtale.TorsorGaloisComponent
