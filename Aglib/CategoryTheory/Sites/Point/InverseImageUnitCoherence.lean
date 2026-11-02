/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Point.InverseImageComparison

/-! # Original unit transport on actual point fibres

The original presheaf section map and structural map of the two supplied points
descend to the original colimits. Identity, composition, coefficient naturality
and change of the actual test functor follow on germs. For an actual supplied
sheaf adjunction this map is the hom of the one original skyscraper-mate Iso.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point.UnitTransport

universe uC vC uD vD uE vE p q r uA vA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (Φ : Point.{p} J) (Ψ : Point.{q} K) (F : C ⥤ D)
  (point : ∀ U, Φ.fiber.obj U → Ψ.fiber.obj (F.obj U))
  (point_naturality : ∀ {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U),
    point V (Φ.fiber.map f x) = Ψ.fiber.map (F.map f) (point U x))
  {A : Type uA} [Category.{vA} A]
  [HasColimitsOfSize.{p, p} A] [HasColimitsOfSize.{q, q} A]

/-- Descend the actual section map and actual structural point values. -/
def map {P : Cᵒᵖ ⥤ A} {Q : Dᵒᵖ ⥤ A} (σ : P ⟶ F.op ⋙ Q) :
    Φ.presheafFiber.obj P ⟶ Ψ.presheafFiber.obj Q :=
  Φ.presheafFiberDesc
    (fun U x => σ.app (op U) ≫ Ψ.toPresheafFiber (F.obj U) (point U x) Q)
    (by
      intro U V f x
      rw [← Category.assoc, σ.naturality f.op, Category.assoc]
      change σ.app (op V) ≫
        (Q.map (F.map f).op ≫ Ψ.toPresheafFiber (F.obj U) (point U x) Q) = _
      rw [Ψ.toPresheafFiber_w]
      exact congrArg (fun y => σ.app (op V) ≫ Ψ.toPresheafFiber (F.obj V) y Q)
        (point_naturality f x).symm)

/-- The whole map retains the original section and point on every actual germ. -/
@[reassoc]
theorem germ_map {P : Cᵒᵖ ⥤ A} {Q : Dᵒᵖ ⥤ A} (σ : P ⟶ F.op ⋙ Q)
    (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x P ≫ map Φ Ψ F point point_naturality σ =
      σ.app (op U) ≫ Ψ.toPresheafFiber (F.obj U) (point U x) Q :=
  Φ.toPresheafFiber_presheafFiberDesc _ _ U x

/-- Ordinary coefficient-section naturality gives the complete fibre naturality square. -/
theorem map_naturality {P P' : Cᵒᵖ ⥤ A} {Q Q' : Dᵒᵖ ⥤ A}
    (σ : P ⟶ F.op ⋙ Q) (τ : P' ⟶ F.op ⋙ Q')
    (a : P ⟶ P') (b : Q ⟶ Q')
    (h : a ≫ τ = σ ≫ Functor.whiskerLeft F.op b) :
    Φ.presheafFiber.map a ≫ map Φ Ψ F point point_naturality τ =
      map Φ Ψ F point point_naturality σ ≫ Ψ.presheafFiber.map b := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  rw [← Category.assoc, Φ.toPresheafFiber_naturality, Category.assoc, germ_map,
    germ_map_assoc, Ψ.toPresheafFiber_naturality]
  have hc := NatTrans.congr_app h (op U)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.op_obj,
    Category.assoc] using
    congrArg (fun k => k ≫ Ψ.toPresheafFiber (F.obj U) (point U x) Q') hc

/-- Changing the actual test functor through its point and section equations preserves the map. -/
theorem map_transport {G : C ⥤ D}
    (point' : ∀ U, Φ.fiber.obj U → Ψ.fiber.obj (G.obj U))
    (point'_naturality : ∀ {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U),
      point' V (Φ.fiber.map f x) = Ψ.fiber.map (G.map f) (point' U x))
    (ϑ : F ⟶ G)
    (hp : ∀ U x, Ψ.fiber.map (ϑ.app U) (point U x) = point' U x)
    {P : Cᵒᵖ ⥤ A} {Q : Dᵒᵖ ⥤ A}
    (σ : P ⟶ F.op ⋙ Q) (τ : P ⟶ G.op ⋙ Q)
    (hσ : σ = τ ≫ Functor.whiskerRight (NatTrans.op ϑ) Q) :
    map Φ Ψ F point point_naturality σ = map Φ Ψ G point' point'_naturality τ := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  rw [germ_map, germ_map, hσ]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.op_app,
    Category.assoc]
  rw [Ψ.toPresheafFiber_w, hp]

/-- Original evaluation legs and an ordinary section-value square give the whole fibre square. -/
theorem map_square_of_values {P : Cᵒᵖ ⥤ A} {Q : Dᵒᵖ ⥤ A} (σ : P ⟶ F.op ⋙ Q)
    {M N : A} (a : Φ.presheafFiber.obj P ⟶ M) (b : Ψ.presheafFiber.obj Q ⟶ N)
    (k : M ⟶ N)
    (source : ∀ U, Φ.fiber.obj U → (P.obj (op U) ⟶ M))
    (target : ∀ V, Ψ.fiber.obj V → (Q.obj (op V) ⟶ N))
    (hsource : ∀ U x, Φ.toPresheafFiber U x P ≫ a = source U x)
    (htarget : ∀ V y, Ψ.toPresheafFiber V y Q ≫ b = target V y)
    (hvalue : ∀ U x, σ.app (op U) ≫ target (F.obj U) (point U x) = source U x ≫ k) :
    map Φ Ψ F point point_naturality σ ≫ b = a ≫ k := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  calc
    _ = σ.app (op U) ≫ (Ψ.toPresheafFiber (F.obj U) (point U x) Q ≫ b) :=
      germ_map_assoc Φ Ψ F point point_naturality σ U x b
    _ = σ.app (op U) ≫ target (F.obj U) (point U x) :=
      congrArg (fun z => σ.app (op U) ≫ z) (htarget _ _)
    _ = source U x ≫ k := hvalue U x
    _ = (Φ.toPresheafFiber U x P ≫ a) ≫ k :=
      congrArg (fun z => z ≫ k) (hsource U x).symm
    _ = _ := Category.assoc _ _ _

section Composition

variable {E : Type uE} [Category.{vE} E] {L : GrothendieckTopology E}
  (Ω : Point.{r} L) (G : D ⥤ E)
  (point' : ∀ U, Ψ.fiber.obj U → Ω.fiber.obj (G.obj U))
  (point'_naturality : ∀ {U V : D} (f : U ⟶ V) (x : Ψ.fiber.obj U),
    point' V (Ψ.fiber.map f x) = Ω.fiber.map (G.map f) (point' U x))
  [HasColimitsOfSize.{r, r} A]

/-- The structural point of a composite is the same two given structural maps. -/
def compPoint : ∀ U, Φ.fiber.obj U → Ω.fiber.obj ((F ⋙ G).obj U) :=
  fun U x => point' (F.obj U) (point U x)

include point_naturality point'_naturality in
/-- Naturality of those same two maps proves composite-point naturality. -/
theorem compPoint_naturality {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U) :
    compPoint Φ Ψ F point Ω G point' V (Φ.fiber.map f x) =
      Ω.fiber.map ((F ⋙ G).map f) (compPoint Φ Ψ F point Ω G point' U x) := by
  change point' (F.obj V) (point V (Φ.fiber.map f x)) = _
  rw [point_naturality, point'_naturality]
  rfl

/-- Composition retains the original section composite and actual point composite. -/
theorem map_comp {P : Cᵒᵖ ⥤ A} {Q : Dᵒᵖ ⥤ A} {R : Eᵒᵖ ⥤ A}
    (σ : P ⟶ F.op ⋙ Q) (τ : Q ⟶ G.op ⋙ R) :
    map Φ Ω (F ⋙ G) (compPoint Φ Ψ F point Ω G point')
        (compPoint_naturality Φ Ψ F point point_naturality Ω G point' point'_naturality)
        (σ ≫ Functor.whiskerLeft F.op τ ≫ (Functor.associator F.op G.op R).inv) =
      map Φ Ψ F point point_naturality σ ≫ map Ψ Ω G point' point'_naturality τ := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  simp only [germ_map, germ_map_assoc, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.op_obj, Functor.comp_obj,
    Category.comp_id, Category.assoc, compPoint]

end Composition

section Identity

/-- Identity structural points and the original identity section give the identity fibre map. -/
theorem map_id {C₀ : Type uC} [Category.{vC} C₀] {J₀ : GrothendieckTopology C₀}
    (Φ₀ : Point.{p} J₀) {A₀ : Type uA} [Category.{vA} A₀]
    [HasColimitsOfSize.{p, p} A₀] (P : C₀ᵒᵖ ⥤ A₀) :
    map Φ₀ Φ₀ (𝟭 C₀) (fun _ x => x) (by intros; rfl) (Functor.leftUnitor P).inv =
      𝟙 (Φ₀.presheafFiber.obj P) := by
  apply Φ₀.presheafFiber_hom_ext
  intro U x
  have h := germ_map Φ₀ Φ₀ (𝟭 C₀) (fun _ x => x) (by intros; rfl)
    (Functor.leftUnitor P).inv U x
  have hi : (Functor.leftUnitor P).inv.app (op U) ≫
      Φ₀.toPresheafFiber ((𝟭 C₀).obj U) x P =
        Φ₀.toPresheafFiber U x P ≫ 𝟙 (Φ₀.presheafFiber.obj P) := by
    change (𝟙 (P.obj (op U))) ≫ Φ₀.toPresheafFiber U x P =
      Φ₀.toPresheafFiber U x P ≫ 𝟙 (Φ₀.presheafFiber.obj P)
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  exact h.trans hi

end Identity

/-- Inverting the two actual unit equivalences gives the original section retraction. -/
theorem inverse_section {A B C : Type*} (Ep : A ≃ B) (Eo : B ≃ C) (c : C → A)
    (h : ∀ x, c (Eo (Ep x)) = x) (z : C) : c z = Ep.symm (Eo.symm z) := by
  have hz := h (Ep.symm (Eo.symm z))
  simpa only [Equiv.apply_symm_apply] using hz

section ActualMate

variable (fiberEquiv : ∀ U, Φ.fiber.obj U ≃ Ψ.fiber.obj (F.obj U))
  (fiberNaturality : ∀ {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U),
    fiberEquiv V (Φ.fiber.map f x) = Ψ.fiber.map (F.map f) (fiberEquiv U x))
  [HasProducts.{p} A] [HasProducts.{q} A] [F.IsContinuous J K]
  (left : Sheaf J A ⥤ Sheaf K A) (adj : left ⊣ F.sheafPushforwardContinuous A J K)

/-- This descended unit is exactly the hom of the one actual supplied-adjunction mate. -/
theorem map_unit_eq_fiberIso (M : Sheaf J A) :
    map Φ Ψ F (fun U x => fiberEquiv U x) fiberNaturality (adj.unit.app M).hom =
      (InverseImageComparison.fiberIso Φ Ψ F fiberEquiv fiberNaturality left adj).hom.app M := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  exact (germ_map Φ Ψ F (fun U x => fiberEquiv U x) fiberNaturality
    (adj.unit.app M).hom U x).trans
      (InverseImageComparison.germ_fiberIso Φ Ψ F fiberEquiv fiberNaturality left adj M U x).symm

end ActualMate

end CategoryTheory.GrothendieckTopology.Point.UnitTransport
