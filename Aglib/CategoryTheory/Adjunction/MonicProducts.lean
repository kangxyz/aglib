/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Monic units and products from original adjuncts

A monic map into a right-adjoint image makes the original unit monic.
For a chosen family of adjunctions, genuine detection of maps into a fixed
object and monic transposes prove monicity of the original product map.
The construction uses the supplied products, coordinates and factor maps.
-/

@[expose] public noncomputable section

universe i v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Limits

section Units

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- A supplied monic right-target map makes the literal original unit monic. -/
theorem mono_unit_app_of_mono_rightTarget {F : C} {M : D}
    (α : F ⟶ R.obj M) [Mono α] : Mono (adj.unit.app F) := by
  have h : adj.unit.app F ≫ R.map ((adj.homEquiv F M).symm α) = α :=
    (adj.homEquiv F M).apply_symm_apply α
  exact mono_of_mono_fac h

/-- Monicity of the unit at the target makes the original left-adjoint map
injective on maps into that target. -/
theorem map_injective_of_mono_unit_app (F : C) [Mono (adj.unit.app F)] (G : C) :
    Function.Injective (fun a : G ⟶ F => L.map a) := by
  intro a b hab
  apply (cancel_mono (adj.unit.app F)).mp
  calc
    a ≫ adj.unit.app F = adj.unit.app G ≫ R.map (L.map a) := adj.unit.naturality a
    _ = adj.unit.app G ≫ R.map (L.map b) :=
      congrArg (fun k => adj.unit.app G ≫ R.map k) hab
    _ = b ≫ adj.unit.app F := (adj.unit.naturality b).symm

end Units

section Products

variable {I : Type i} {C : Type u₁} [Category.{v₁} C]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  {L : ∀ i, C ⥤ D i} {R : ∀ i, D i ⥤ C} (adj : ∀ i, L i ⊣ R i)

/-- The original product of the supplied adjoints of the coordinate maps. -/
def adjunctionProduct (F : C) (M : ∀ i, D i)
    [HasProduct (fun i => (R i).obj (M i))] (a : ∀ i, (L i).obj F ⟶ M i) :
    F ⟶ ∏ᶜ fun i => (R i).obj (M i) :=
  Pi.lift fun i => (adj i).homEquiv F (M i) (a i)

/-- Each coordinate is the original unit followed by the right image of the
supplied coordinate map. -/
@[reassoc]
theorem adjunctionProduct_π (F : C) (M : ∀ i, D i)
    [HasProduct (fun i => (R i).obj (M i))] (a : ∀ i, (L i).obj F ⟶ M i) (i : I) :
    adjunctionProduct adj F M a ≫ Pi.π (fun i => (R i).obj (M i)) i =
      (adj i).unit.app F ≫ (R i).map (a i) :=
  Pi.lift_comp_π (fun k => (adj k).homEquiv F (M k) (a k)) i

/-- Detection into `F` and the original monic adjunct factorizations make the
literal product of the supplied `q` coordinates monic. Only its product is needed. -/
theorem mono_lift_of_monic_adjunct_factors (F : C)
    (hL : ∀ (G : C) (g h : G ⟶ F), (∀ i, (L i).map g = (L i).map h) → g = h)
    (M : ∀ i, D i) (a : ∀ i, (L i).obj F ⟶ M i) [∀ i, Mono (a i)]
    {T : I → C} [HasProduct T] (q : ∀ i, F ⟶ T i)
    (v : ∀ i, T i ⟶ (R i).obj (M i))
    (hfac : ∀ i, q i ≫ v i = (adj i).homEquiv F (M i) (a i)) :
    Mono (Pi.lift q) where
  right_cancellation {G} g h he := by
    apply hL G g h
    intro i
    apply (cancel_mono (a i)).mp
    apply ((adj i).homEquiv G (M i)).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
    let π := Pi.π T i
    have hp : Pi.lift q ≫ π = q i := Pi.lift_comp_π q i
    have hcoord : g ≫ q i = h ≫ q i := by
      have hproj : g ≫ (Pi.lift q ≫ π) = h ≫ (Pi.lift q ≫ π) :=
        (Category.assoc g (Pi.lift q) π).symm.trans
          ((congrArg (fun k => k ≫ π) he).trans (Category.assoc h (Pi.lift q) π))
      exact (congrArg (fun k => g ≫ k) hp.symm).trans
        (hproj.trans (congrArg (fun k => h ≫ k) hp))
    exact (congrArg (fun k => g ≫ k) (hfac i).symm).trans
      ((Category.assoc g (q i) (v i)).symm.trans
        ((congrArg (fun k => k ≫ v i) hcoord).trans
          ((Category.assoc h (q i) (v i)).trans
            (congrArg (fun k => h ≫ k) (hfac i)))))

/-- Monic coordinate maps give a monic original adjunction product whenever the
chosen left adjoints genuinely detect maps into the source object. -/
theorem mono_adjunctionProduct (F : C)
    (hL : ∀ (G : C) (g h : G ⟶ F), (∀ i, (L i).map g = (L i).map h) → g = h)
    (M : ∀ i, D i) [HasProduct (fun i => (R i).obj (M i))]
    (a : ∀ i, (L i).obj F ⟶ M i) [∀ i, Mono (a i)] :
    Mono (adjunctionProduct adj F M a) := by
  exact mono_lift_of_monic_adjunct_factors adj F hL M a
    (fun i => (adj i).homEquiv F (M i) (a i)) (fun _ => 𝟙 _) (fun _ => Category.comp_id _)

/-- The literal product of the units of the chosen adjunctions. -/
def unitProduct (F : C) [HasProduct (fun i => (R i).obj ((L i).obj F))] :
    F ⟶ ∏ᶜ fun i => (R i).obj ((L i).obj F) :=
  adjunctionProduct adj F (fun i => (L i).obj F) (fun _ => 𝟙 _)

/-- Every projection of the unit product is the original unit component. -/
@[reassoc]
theorem unitProduct_π (F : C) [HasProduct (fun i => (R i).obj ((L i).obj F))] (i : I) :
    unitProduct adj F ≫ Pi.π (fun i => (R i).obj ((L i).obj F)) i = (adj i).unit.app F := by
  have h : unitProduct adj F ≫ Pi.π (fun i => (R i).obj ((L i).obj F)) i =
      (adj i).homEquiv F _ (𝟙 _) := adjunctionProduct_π adj F _ (fun _ => 𝟙 _) i
  exact h.trans ((adj i).homEquiv_id F)

/-- The original unit product is monic under genuine detection into its source. -/
theorem mono_unitProduct (F : C) [HasProduct (fun i => (R i).obj ((L i).obj F))]
    (hL : ∀ (G : C) (g h : G ⟶ F), (∀ i, (L i).map g = (L i).map h) → g = h) :
    Mono (unitProduct adj F) :=
  mono_adjunctionProduct adj F hL _ (fun _ => 𝟙 _)

end Products

section WholeProducts

variable {I : Type i} {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {F : C} {T : I → D} [HasProduct T] {W : I → C} [HasProduct W]

/-- Transpose the coordinates of the supplied whole product map and transport
them through the actual component isomorphisms. -/
def productTranspose (f : L.obj F ⟶ ∏ᶜ T) (e : ∀ i, R.obj (T i) ≅ W i) :
    F ⟶ ∏ᶜ W :=
  Pi.lift fun i => adj.homEquiv F (T i) (f ≫ Pi.π T i) ≫ (e i).hom

/-- Every projection retains the original coordinate transpose and isomorphism. -/
@[reassoc]
theorem productTranspose_π (f : L.obj F ⟶ ∏ᶜ T) (e : ∀ i, R.obj (T i) ≅ W i)
    (i : I) :
    adj.productTranspose f e ≫ Pi.π W i =
      adj.homEquiv F (T i) (f ≫ Pi.π T i) ≫ (e i).hom :=
  Pi.lift_comp_π _ i

/-- The original tuple is the whole transpose followed by the actual product
comparison and the product of the supplied component isomorphisms. -/
theorem productTranspose_eq [HasProduct (fun i => R.obj (T i))]
    (f : L.obj F ⟶ ∏ᶜ T) (e : ∀ i, R.obj (T i) ≅ W i) :
    adj.productTranspose f e =
      adj.homEquiv F (∏ᶜ T) f ≫ piComparison R T ≫ Limits.Pi.map (fun i => (e i).hom) := by
  apply Pi.hom_ext
  intro i
  calc
    adj.productTranspose f e ≫ Pi.π W i =
        adj.homEquiv F (T i) (f ≫ Pi.π T i) ≫ (e i).hom :=
      productTranspose_π adj f e i
    _ = (adj.homEquiv F (∏ᶜ T) f ≫ R.map (Pi.π T i)) ≫ (e i).hom :=
      congrArg (fun k => k ≫ (e i).hom) (adj.homEquiv_naturality_right f (Pi.π T i))
    _ = (adj.homEquiv F (∏ᶜ T) f ≫ piComparison R T ≫ Limits.Pi.map (fun i => (e i).hom)) ≫
        Pi.π W i := by
      simp only [Category.assoc, Pi.map_π, piComparison_comp_π_assoc]

/-- A monic whole product map has a monic original transported tuple if the
left adjoint reflects monomorphisms. Its coordinates need not be monic. -/
theorem mono_productTranspose [L.ReflectsMonomorphisms]
    (f : L.obj F ⟶ ∏ᶜ T) [Mono f] (e : ∀ i, R.obj (T i) ≅ W i) :
    Mono (adj.productTranspose f e) := by
  have : PreservesLimitsOfSize.{i, i} R := adj.rightAdjoint_preservesLimits
  have : HasProduct (fun i => R.obj (T i)) :=
    hasLimit_of_iso (Discrete.compNatIsoDiscrete T R)
  rw [productTranspose_eq]
  infer_instance

end WholeProducts

end CategoryTheory.Adjunction

namespace CategoryTheory.Limits

variable {I : Type i} {C : Type u₁} [Category.{v₁} C]
  {P : C} {A B : I → C} [HasProduct A] [HasProduct B]

/-- The actual product of coordinate factorizations has the original composite. -/
theorem Pi.lift_comp_map_of_factors (a : ∀ i, P ⟶ B i) (b : ∀ i, P ⟶ A i)
    (c : ∀ i, A i ⟶ B i) (h : ∀ i, b i ≫ c i = a i) :
    Pi.lift b ≫ Pi.map c = Pi.lift a := by
  apply Pi.hom_ext
  intro i
  calc
    (Pi.lift b ≫ Pi.map c) ≫ Pi.π B i = Pi.lift b ≫ (Pi.map c ≫ Pi.π B i) :=
      Category.assoc _ _ _
    _ = Pi.lift b ≫ (Pi.π A i ≫ c i) :=
      congrArg (fun k => Pi.lift b ≫ k) (Pi.map_π c i)
    _ = (Pi.lift b ≫ Pi.π A i) ≫ c i := (Category.assoc _ _ _).symm
    _ = b i ≫ c i := congrArg (fun k => k ≫ c i) (Pi.lift_comp_π b i)
    _ = a i := h i
    _ = Pi.lift a ≫ Pi.π B i := (Pi.lift_comp_π a i).symm

/-- Factoring the coordinates of a monic original product makes the source
product monic, using the actual chosen product maps. -/
theorem Pi.mono_lift_of_factors (a : ∀ i, P ⟶ B i) (b : ∀ i, P ⟶ A i)
    (c : ∀ i, A i ⟶ B i) (h : ∀ i, b i ≫ c i = a i) [Mono (Pi.lift a)] :
    Mono (Pi.lift b) :=
  mono_of_mono_fac (Pi.lift_comp_map_of_factors a b c h)

end CategoryTheory.Limits
