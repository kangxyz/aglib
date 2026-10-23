/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange

/-! # Transporting the actual vertical composition law through homology -/

@[expose] public section
namespace CategoryTheory
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- Transport a proved composition square through a functor and its actual endpoint isomorphism. -/
theorem mapped_vertical_transport (H : D ⥤ E) {R R' : C ⥤ D} (c : R ≅ R')
    {X Y : C} (p : X ⟶ Y) {Z Z' : D} (d : Z ⟶ Z')
    (v : Z' ⟶ R'.obj X) (u : Z ⟶ R.obj X)
    (h : d ≫ v = u ≫ c.hom.app X)
    {P Q : E} (s : P ⟶ H.obj Z) (e : Q ≅ H.obj (R.obj Y))
    (b : P ⟶ Q) (hb : b = s ≫ H.map u ≫ H.map (R.map p) ≫ e.inv) :
    s ≫ H.map d ≫ H.map v ≫ H.map (R'.map p) =
      b ≫ e.hom ≫ H.map (c.hom.app Y) := by
  rw [hb]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp_assoc, h, H.map_comp, Category.assoc]
  have hn := congrArg H.map (c.hom.naturality p)
  simp only [H.map_comp] at hn
  rw [← hn]

/-- Vertical transport for supplied actual maps and their canonical factorizations. -/
theorem mapped_vertical_pasting_actual (H : D ⥤ E)
    {R R' : C ⥤ D} (c : R ≅ R') {X Y : C} (p : X ⟶ Y)
    {Z Z' : D} (d : Z ⟶ Z') (v : Z' ⟶ R'.obj X) (u : Z ⟶ R.obj X)
    (h : d ≫ v = u ≫ c.hom.app X)
    {P Q : E} (s : P ≅ H.obj Z) (e : Q ≅ H.obj (R.obj Y))
    (t : H.obj (R.obj X) ≅ Q) (b : P ⟶ Q)
    (hb : b ≫ t.inv = s.hom ≫ H.map u)
    (ht : t.hom = H.map (R.map p) ≫ e.inv)
    (iS : P ≅ H.obj Z') (iT : H.obj (R'.obj X) ≅ H.obj (R'.obj Y))
    (iE : Q ≅ H.obj (R'.obj Y))
    (hS : iS.hom = s.hom ≫ H.map d)
    (hT : iT.hom = H.map (R'.map p))
    (hE : iE.hom = e.hom ≫ H.map (c.hom.app Y)) :
    iS.hom ≫ H.map v ≫ iT.hom = b ≫ iE.hom := by
  have hb' := congrArg (fun k => k ≫ t.hom) hb
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hb'
  rw [ht] at hb'
  rw [hS, hT, hE]
  simpa only [Category.assoc] using
    mapped_vertical_transport H c p d v u h s.hom e b hb'

section ActualWhiskeredTarget
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (J : A ⥤ B) (H : C ⥤ D) {L M : B ⥤ C} (β : L ⟶ M)
  {U V : A ⥤ D} (s : U ≅ J ⋙ L ⋙ H) (t : J ⋙ M ⋙ H ≅ V)
  (τ : U ⟶ V)

/-- The literal component factorization with the actual transported map opaque. -/
def ActualWhiskeredTargetInverseEquation (F : A) : Prop :=
  τ.app F ≫ t.inv.app F = s.hom.app F ≫ H.map (β.app (J.obj F))

/-- The original whole-transformation alias supplies target-inverse cancellation. -/
theorem actualWhiskeredTargetInverseEquation_of_transport
    (hτ : τ = s.hom ≫ Functor.whiskerLeft J (Functor.whiskerRight β H) ≫ t.hom)
    (F : A) : ActualWhiskeredTargetInverseEquation J H β s t τ F := by
  subst τ
  dsimp only [ActualWhiskeredTargetInverseEquation, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Extract the actual component equation without unfolding the transported map. -/
theorem actualWhiskeredTargetInverseEquation_eq (F : A)
    (h : ActualWhiskeredTargetInverseEquation J H β s t τ F) :
    τ.app F ≫ t.inv.app F = s.hom.app F ≫ H.map (β.app (J.obj F)) := h

end ActualWhiskeredTarget

section SharedMappedEquations
variable {D E : Type*} [Category* D] [Category* E]

/-- The original target-inverse factorization, with all component maps explicit. -/
def MappedTargetInverseEquation (H : D ⥤ E) {X Y : D} (a : X ⟶ Y)
    {P Q : E} (s : P ≅ H.obj X) (t : Q ≅ H.obj Y) (b : P ⟶ Q) : Prop :=
  b ≫ t.hom = s.hom ≫ H.map a

/-- The literal higher vertical equation, retaining its actual endpoint isomorphisms. -/
def MappedVerticalPastingEquation (H : D ⥤ E) {X Y : D} (v : X ⟶ Y)
    {P Q W : E} (s : P ≅ H.obj X) (t : H.obj Y ≅ W)
    (e : Q ≅ W) (b : P ⟶ Q) : Prop :=
  s.hom ≫ H.map v ≫ t.hom = b ≫ e.hom

end SharedMappedEquations

/-- Only the generic boundary turns the whole transport predicate into its component form. -/
theorem mappedTargetInverseEquation_of_whiskered
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (J : A ⥤ B) (H : C ⥤ D) {L M : B ⥤ C} (β : L ⟶ M)
    {U V : A ⥤ D} (s : U ≅ J ⋙ L ⋙ H) (t : J ⋙ M ⋙ H ≅ V)
    (τ : U ⟶ V) (F : A)
    (h : ActualWhiskeredTargetInverseEquation J H β s t τ F) :
    MappedTargetInverseEquation H (β.app (J.obj F)) (s.app F) (t.app F).symm
      (τ.app F) := h

/-- Vertical pasting uses only the shared actual-map factor and native endpoint aliases. -/
theorem mapped_vertical_pasting_actual_equation
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (H : D ⥤ E)
    {R R' : C ⥤ D} (c : R ≅ R') {X Y : C} (p : X ⟶ Y)
    {Z Z' : D} (d : Z ⟶ Z') (v : Z' ⟶ R'.obj X) (u : Z ⟶ R.obj X)
    (h : d ≫ v = u ≫ c.hom.app X)
    {P Q : E} (s : P ≅ H.obj Z) (e : Q ≅ H.obj (R.obj Y))
    (t : H.obj (R.obj X) ≅ Q) (b : P ⟶ Q)
    (hb : MappedTargetInverseEquation H u s t.symm b)
    (ht : t.hom = H.map (R.map p) ≫ e.inv)
    (iS : P ≅ H.obj Z') (iT : H.obj (R'.obj X) ≅ H.obj (R'.obj Y))
    (iE : Q ≅ H.obj (R'.obj Y))
    (hS : iS.hom = s.hom ≫ H.map d)
    (hT : iT.hom = H.map (R'.map p))
    (hE : iE.hom = e.hom ≫ H.map (c.hom.app Y)) :
    MappedVerticalPastingEquation H v iS iT iE b :=
  mapped_vertical_pasting_actual H c p d v u h s e t b hb ht iS iT iE hS hT hE

/-- Read the literal vertical equation without unfolding any actual map. -/
theorem mappedVerticalPastingEquation_eq
    {D E : Type*} [Category* D] [Category* E]
    (H : D ⥤ E) {X Y : D} (v : X ⟶ Y)
    {P Q W : E} (s : P ≅ H.obj X) (t : H.obj Y ≅ W)
    (e : Q ≅ W) (b : P ⟶ Q)
    (h : MappedVerticalPastingEquation H v s t e b) :
    s.hom ≫ H.map v ≫ t.hom = b ≫ e.hom := h

end CategoryTheory
