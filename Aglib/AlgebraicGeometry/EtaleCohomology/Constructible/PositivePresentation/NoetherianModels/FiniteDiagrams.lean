/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.HomAbove
public import Mathlib.CategoryTheory.FinCategory.Basic

/-! # Actual finite bounded coefficient diagrams over one model stage

Object models are placed at one common stage. Original Hom continuity then
descends the actual finite arrows; its eventual-equality statement descends
the actual functor equations. The resulting finite functor retains a native
natural isomorphism after the original structural inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u v

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

private theorem transported_hom_commutes
    {C D K : Type*} [Category* C] [Category* D] [Category* K]
    (F : C ⥤ K) (E : C ⥤ D) (G : D ⥤ K) (b : F ≅ E ⋙ G)
    {A B : C} {P Q : K} (eA : F.obj A ≅ P) (eB : F.obj B ≅ Q)
    (t : A ⟶ B) (f : P ⟶ Q) (ht : F.map t ≫ eB.hom = eA.hom ≫ f) :
    G.map (E.map t) ≫ ((b.app B).symm ≪≫ eB).hom =
      ((b.app A).symm ≪≫ eA).hom ≫ f := by
  change G.map (E.map t) ≫ b.inv.app B ≫ eB.hom = (b.inv.app A ≫ eA.hom) ≫ f
  rw [Category.assoc (b.inv.app A) eA.hom f]
  have hb : G.map (E.map t) ≫ b.inv.app B = b.inv.app A ≫ F.map t :=
    b.inv.naturality t
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ eB.hom) hb)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => b.inv.app A ≫ k) ht))

private theorem lifted_hom_commutes
    {C D K : Type*} [Category* C] [Category* D] [Category* K]
    (F : C ⥤ K) (E : C ⥤ D) (G : D ⥤ K) (b : F ≅ E ⋙ G)
    {A B : C} {P Q : K} (eA : F.obj A ≅ P) (eB : F.obj B ≅ Q)
    (k : E.obj A ⟶ E.obj B) (f : P ⟶ Q)
    (hk : b.hom.app A ≫ G.map k = (eA.hom ≫ f ≫ eB.inv) ≫ b.hom.app B) :
    G.map k ≫ ((b.app B).symm ≪≫ eB).hom =
      ((b.app A).symm ≪≫ eA).hom ≫ f := by
  change G.map k ≫ b.inv.app B ≫ eB.hom = (b.inv.app A ≫ eA.hom) ≫ f
  rw [Category.assoc (b.inv.app A) eA.hom f]
  apply (cancel_epi (b.hom.app A)).mp
  simp only [← Category.assoc]
  rw [hk]
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id]

private def insertHoms {C V P : Type*} [Category* C] [DecidableEq P]
    (src tgt : P → V) (M : V → C) (a : P) (s : Finset P)
    (k : M (src a) ⟶ M (tgt a))
    (g : ∀ p ∈ s, M (src p) ⟶ M (tgt p))
    (p : P) (hp : p ∈ insert a s) : M (src p) ⟶ M (tgt p) := by
  exact if h : p = a then by subst p; exact k
    else g p ((Finset.mem_insert.mp hp).resolve_left h)

private theorem insertHoms_commute {C D V P : Type*} [Category* C] [Category* D]
    [DecidableEq P]
    (src tgt : P → V) (M : V → C) (L : V → D) (F : C ⥤ D)
    (e : ∀ v, F.obj (M v) ≅ L v) (f : ∀ p, L (src p) ⟶ L (tgt p))
    (a : P) (s : Finset P) (k : M (src a) ⟶ M (tgt a))
    (g : ∀ p ∈ s, M (src p) ⟶ M (tgt p))
    (hk : F.map k ≫ (e (tgt a)).hom = (e (src a)).hom ≫ f a)
    (hg : ∀ p hp, F.map (g p hp) ≫ (e (tgt p)).hom = (e (src p)).hom ≫ f p) :
    ∀ p hp, F.map (insertHoms src tgt M a s k g p hp) ≫ (e (tgt p)).hom =
      (e (src p)).hom ≫ f p := by
  intro p hp
  by_cases h : p = a
  · subst p
    have hi : insertHoms src tgt M a s k g a hp = k := dite_eq_left rfl
    exact (congrArg (fun t => F.map t ≫ (e (tgt a)).hom) hi).trans hk
  · have hi : insertHoms src tgt M a s k g p hp =
        g p ((Finset.mem_insert.mp hp).resolve_left h) := dite_eq_right h
    exact (congrArg (fun t => F.map t ≫ (e (tgt p)).hom) hi).trans
      (hg p ((Finset.mem_insert.mp hp).resolve_left h))

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (n : ℕ)

/-- An actual canonical coefficient model exists above every specified stage.
The witness includes its original structural inverse-image isomorphism. -/
def HasStageModel : ObjectProperty (BoundedPresentation.Coefficient c.pt.unop n) :=
  fun A => ∀ i₀ : I, ∃ (i : I) (_ : i₀ ⟶ i)
    (M : BoundedPresentation.Coefficient (X.obj i).unop n),
    BoundedPresentation.finiteColimitStages (X.obj i).unop n M ∧
      Nonempty ((boundedInverseImage (c.ι.app i).unop n).obj M ≅ A)

variable [IsFiltered I]
  [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop] (hc : IsColimit c)

private theorem exists_objectModels_above {V : Type v} [Finite V]
    (i₀ : I) (L : V → BoundedPresentation.Coefficient c.pt.unop n)
    (hL : ∀ v, HasStageModel X c n (L v)) :
    ∃ (i : I) (_ : i₀ ⟶ i) (M : V → BoundedPresentation.Coefficient (X.obj i).unop n),
      (∀ v, BoundedPresentation.finiteColimitStages (X.obj i).unop n (M v)) ∧
      Nonempty (∀ v, (boundedInverseImage (c.ι.app i).unop n).obj (M v) ≅ L v) := by
  classical
  choose j q N hN he using fun v : V => hL v i₀
  obtain ⟨i, r, g, _⟩ := IsFiltered.wideSpan q
  let M (v : V) := (boundedInverseImage (X.map (g v)).unop n).obj (N v)
  refine ⟨i, r, M, ?_, ⟨fun v => ?_⟩⟩
  · intro v
    exact finiteColimitStage_inverseImage (X.map (g v)).unop n (N v) (hN v)
  · exact ((boundedConeCompIso X c n (g v)).app (N v)).symm ≪≫ (he v).some

include hc in
private theorem exists_finiteHoms_above {V P : Type v} [Finite P]
    (src tgt : P → V) (L : V → BoundedPresentation.Coefficient c.pt.unop n)
    (f : ∀ p, L (src p) ⟶ L (tgt p))
    (i₀ : I) (M₀ : V → BoundedPresentation.Coefficient (X.obj i₀).unop n)
    (hM₀ : ∀ v, BoundedPresentation.finiteColimitStages (X.obj i₀).unop n (M₀ v))
    (e₀ : ∀ v, (boundedInverseImage (c.ι.app i₀).unop n).obj (M₀ v) ≅ L v) :
    ∃ (i : I) (_ : i₀ ⟶ i) (M : V → BoundedPresentation.Coefficient (X.obj i).unop n),
      (∀ v, BoundedPresentation.finiteColimitStages (X.obj i).unop n (M v)) ∧
      ∃ (e : ∀ v, (boundedInverseImage (c.ι.app i).unop n).obj (M v) ≅ L v)
        (g : ∀ p, M (src p) ⟶ M (tgt p)),
        ∀ p, (boundedInverseImage (c.ι.app i).unop n).map (g p) ≫ (e (tgt p)).hom =
          (e (src p)).hom ≫ f p := by
  classical
  let : Fintype P := Fintype.ofFinite P
  have main (s : Finset P) :
      ∃ (i : I) (_ : i₀ ⟶ i) (M : V → BoundedPresentation.Coefficient (X.obj i).unop n),
        (∀ v, BoundedPresentation.finiteColimitStages (X.obj i).unop n (M v)) ∧
        ∃ (e : ∀ v, (boundedInverseImage (c.ι.app i).unop n).obj (M v) ≅ L v)
          (g : ∀ p ∈ s, M (src p) ⟶ M (tgt p)),
          ∀ p hp, (boundedInverseImage (c.ι.app i).unop n).map (g p hp) ≫
            (e (tgt p)).hom = (e (src p)).hom ≫ f p := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨i₀, 𝟙 _, M₀, hM₀, e₀, fun p hp => by simp at hp, ?_⟩
      intro p hp
      simp at hp
    | @insert a s _ha ih =>
      obtain ⟨i, r, M, hM, e, g, hg⟩ := ih
      let f₀ := (e (src a)).hom ≫ f a ≫ (e (tgt a)).inv
      obtain ⟨j, q, k, hk⟩ := exists_boundedHom_above X c i hc n
        (M (src a)) (hM (src a)) (M (tgt a)) f₀
      let E := boundedInverseImage (X.map q).unop n
      let G := boundedInverseImage (c.ι.app j).unop n
      let b := boundedConeCompIso X c n q
      let M' (v : V) := E.obj (M v)
      let e' (v : V) : G.obj (M' v) ≅ L v := (b.app (M v)).symm ≪≫ e v
      let g' := insertHoms src tgt M' a s k (fun p hp => E.map (g p hp))
      refine ⟨j, r ≫ q, M', ?_, e', g', ?_⟩
      · intro v
        exact finiteColimitStage_inverseImage (X.map q).unop n (M v) (hM v)
      · exact insertHoms_commute src tgt M' L G e' f a s k
          (fun p hp => E.map (g p hp))
          (lifted_hom_commutes (boundedInverseImage (c.ι.app i).unop n) E G b
            (e (src a)) (e (tgt a)) k (f a) hk)
          (fun p hp => transported_hom_commutes
            (boundedInverseImage (c.ι.app i).unop n) E G b
              (e (src p)) (e (tgt p)) (g p hp) (f p) (hg p hp))
  obtain ⟨i, q, M, hM, e, g, hg⟩ := main Finset.univ
  exact ⟨i, q, M, hM, e, fun p => g p (Finset.mem_univ p),
    fun p => hg p (Finset.mem_univ p)⟩

private abbrev EquationIndex (J : Type v) [SmallCategory J] :=
  J ⊕ Σ x : J, Σ y : J, Σ z : J, (x ⟶ y) × (y ⟶ z)

private def equationSource {J : Type v} [SmallCategory J] : EquationIndex J → J
  | .inl x => x
  | .inr a => a.1

private def equationTarget {J : Type v} [SmallCategory J] : EquationIndex J → J
  | .inl x => x
  | .inr a => a.2.2.1

private def equationLeft {C : Type*} [Category* C] {J : Type v} [SmallCategory J]
    (M : J → C) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)) :
    ∀ a : EquationIndex J, M (equationSource a) ⟶ M (equationTarget a)
  | .inl x => g (𝟙 x)
  | .inr ⟨_, _, _, f, h⟩ => g (f ≫ h)

private def equationRight {C : Type*} [Category* C] {J : Type v} [SmallCategory J]
    (M : J → C) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)) :
    ∀ a : EquationIndex J, M (equationSource a) ⟶ M (equationTarget a)
  | .inl x => 𝟙 (M x)
  | .inr ⟨_, _, _, f, h⟩ => g f ≫ g h

private theorem equationLeft_map {C D : Type*} [Category* C] [Category* D]
    {J : Type v} [SmallCategory J] (E : C ⥤ D)
    (M : J → C) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)) (a : EquationIndex J) :
    E.map (equationLeft M g a) =
      equationLeft (fun x => E.obj (M x)) (fun f => E.map (g f)) a := by
  cases a with
  | inl x => rfl
  | inr a => rcases a with ⟨x, y, z, f, h⟩; rfl

private theorem equationRight_map {C D : Type*} [Category* C] [Category* D]
    {J : Type v} [SmallCategory J] (E : C ⥤ D)
    (M : J → C) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)) (a : EquationIndex J) :
    E.map (equationRight M g a) =
      equationRight (fun x => E.obj (M x)) (fun f => E.map (g f)) a := by
  cases a with
  | inl x => exact E.map_id _
  | inr a => rcases a with ⟨x, y, z, f, h⟩; exact E.map_comp _ _

private theorem equations_insert_map {C D : Type*} [Category* C] [Category* D]
    {J : Type v} [SmallCategory J] [DecidableEq (EquationIndex J)] (E : C ⥤ D)
    (M : J → C) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y))
    (a : EquationIndex J) (s : Finset (EquationIndex J))
    (ha : E.map (equationLeft M g a) = E.map (equationRight M g a))
    (hs : ∀ t ∈ s, equationLeft M g t = equationRight M g t) :
    ∀ t ∈ insert a s,
      equationLeft (fun x => E.obj (M x)) (fun f => E.map (g f)) t =
        equationRight (fun x => E.obj (M x)) (fun f => E.map (g f)) t := by
  intro t ht
  have h : E.map (equationLeft M g t) = E.map (equationRight M g t) := by
    rcases Finset.mem_insert.mp ht with h | h
    · subst t
      exact ha
    · exact congrArg E.map (hs t h)
  exact (equationLeft_map E M g t).symm.trans (h.trans (equationRight_map E M g t))

private theorem equation_eq_after_map {C D : Type*} [Category* C] [Category* D]
    {J : Type v} [SmallCategory J] (L : J ⥤ D)
    (M : J → C) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y))
    (E : C ⥤ D) (e : ∀ x, E.obj (M x) ≅ L.obj x)
    (hg : ∀ {x y : J} (f : x ⟶ y), E.map (g f) ≫ (e y).hom = (e x).hom ≫ L.map f)
    (a : EquationIndex J) : E.map (equationLeft M g a) = E.map (equationRight M g a) := by
  cases a with
  | inl x =>
    apply (cancel_mono (e x).hom).mp
    change E.map (g (𝟙 x)) ≫ (e x).hom = E.map (𝟙 (M x)) ≫ (e x).hom
    rw [hg, E.map_id, L.map_id, Category.id_comp, Category.comp_id]
  | inr a =>
    rcases a with ⟨x, y, z, f, h⟩
    apply (cancel_mono (e z).hom).mp
    change E.map (g (f ≫ h)) ≫ (e z).hom = E.map (g f ≫ g h) ≫ (e z).hom
    calc
      _ = (e x).hom ≫ L.map (f ≫ h) := hg _
      _ = (e x).hom ≫ L.map f ≫ L.map h := by rw [L.map_comp]
      _ = (E.map (g f) ≫ (e y).hom) ≫ L.map h := by rw [hg, Category.assoc]
      _ = E.map (g f) ≫ (E.map (g h) ≫ (e z).hom) := by rw [Category.assoc, hg]
      _ = _ := by rw [E.map_comp, Category.assoc]

include hc in
private theorem exists_functorLaws_above {J : Type v} [SmallCategory J] [FinCategory J]
    (L : J ⥤ BoundedPresentation.Coefficient c.pt.unop n) (i₀ : I)
    (M₀ : J → BoundedPresentation.Coefficient (X.obj i₀).unop n)
    (hM₀ : ∀ x, BoundedPresentation.finiteColimitStages (X.obj i₀).unop n (M₀ x))
    (e₀ : ∀ x, (boundedInverseImage (c.ι.app i₀).unop n).obj (M₀ x) ≅ L.obj x)
    (g₀ : ∀ {x y : J}, (x ⟶ y) → (M₀ x ⟶ M₀ y))
    (hg₀ : ∀ {x y : J} (f : x ⟶ y),
      (boundedInverseImage (c.ι.app i₀).unop n).map (g₀ f) ≫ (e₀ y).hom =
        (e₀ x).hom ≫ L.map f) :
    ∃ (i : I) (_ : i₀ ⟶ i) (M : J → BoundedPresentation.Coefficient (X.obj i).unop n),
      (∀ x, BoundedPresentation.finiteColimitStages (X.obj i).unop n (M x)) ∧
      ∃ (e : ∀ x, (boundedInverseImage (c.ι.app i).unop n).obj (M x) ≅ L.obj x)
        (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)),
        (∀ {x y : J} (f : x ⟶ y),
          (boundedInverseImage (c.ι.app i).unop n).map (g f) ≫ (e y).hom =
            (e x).hom ≫ L.map f) ∧
        ∀ a : EquationIndex J, equationLeft M g a = equationRight M g a := by
  classical
  have main (s : Finset (EquationIndex J)) :
      ∃ (i : I) (_ : i₀ ⟶ i) (M : J → BoundedPresentation.Coefficient (X.obj i).unop n),
        (∀ x, BoundedPresentation.finiteColimitStages (X.obj i).unop n (M x)) ∧
        ∃ (e : ∀ x, (boundedInverseImage (c.ι.app i).unop n).obj (M x) ≅ L.obj x)
          (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)),
          (∀ {x y : J} (f : x ⟶ y),
            (boundedInverseImage (c.ι.app i).unop n).map (g f) ≫ (e y).hom =
              (e x).hom ≫ L.map f) ∧
          ∀ a ∈ s, equationLeft M g a = equationRight M g a := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨i₀, 𝟙 _, M₀, hM₀, e₀, g₀, hg₀, fun a ha => by simp at ha⟩
    | @insert a s _ha ih =>
      obtain ⟨i, r, M, hM, e, g, hg, hrel⟩ := ih
      have heq := equation_eq_after_map L M g
        (boundedInverseImage (c.ι.app i).unop n) e hg a
      obtain ⟨j, q, hq⟩ := boundedHom_eventually_equal_above X c i hc n
        (M (equationSource a)) (hM _) (M (equationTarget a))
        (equationLeft M g a) (equationRight M g a) heq
      let E := boundedInverseImage (X.map q).unop n
      let G := boundedInverseImage (c.ι.app j).unop n
      let b := boundedConeCompIso X c n q
      let M' (x : J) := E.obj (M x)
      let e' (x : J) : G.obj (M' x) ≅ L.obj x := (b.app (M x)).symm ≪≫ e x
      let g' {x y : J} (f : x ⟶ y) : M' x ⟶ M' y := E.map (g f)
      refine ⟨j, r ≫ q, M', ?_, e', g', ?_, ?_⟩
      · intro x
        exact finiteColimitStage_inverseImage (X.map q).unop n (M x) (hM x)
      · intro x y f
        exact transported_hom_commutes (boundedInverseImage (c.ι.app i).unop n)
          E G b (e x) (e y) (g f) (L.map f) (hg f)
      · exact equations_insert_map E M g a s hq hrel
  obtain ⟨i, q, M, hM, e, g, hg, hrel⟩ := main Finset.univ
  exact ⟨i, q, M, hM, e, g, hg, fun a => hrel a (Finset.mem_univ a)⟩

include hc in
/-- Actual object models and original bounded Hom continuity descend the
whole supplied finite diagram, including all arrows and functor equations. -/
theorem exists_finiteDiagram_model {J : Type v} [SmallCategory J] [FinCategory J]
    (i₀ : I) (L : J ⥤ BoundedPresentation.Coefficient c.pt.unop n)
    (hL : ∀ x, HasStageModel X c n (L.obj x)) :
    ∃ (i : I) (_ : i₀ ⟶ i) (Lᵢ : J ⥤ BoundedPresentation.Coefficient (X.obj i).unop n),
      (∀ x, BoundedPresentation.finiteColimitStages (X.obj i).unop n (Lᵢ.obj x)) ∧
      Nonempty (Lᵢ ⋙ boundedInverseImage (c.ι.app i).unop n ≅ L) := by
  classical
  obtain ⟨i, q, M, hM, ⟨e⟩⟩ := exists_objectModels_above X c n i₀ L.obj hL
  let A := Σ x : J, Σ y : J, x ⟶ y
  obtain ⟨j, r, N, hN, e', g', hg'⟩ := exists_finiteHoms_above X c n hc
    (fun a : A => a.1) (fun a : A => a.2.1) L.obj
    (fun a : A => L.map a.2.2) i M hM e
  let g {x y : J} (f : x ⟶ y) : N x ⟶ N y := g' ⟨x, y, f⟩
  have hg {x y : J} (f : x ⟶ y) :
      (boundedInverseImage (c.ι.app j).unop n).map (g f) ≫ (e' y).hom =
        (e' x).hom ≫ L.map f := hg' ⟨x, y, f⟩
  obtain ⟨k, s, P, hP, e'', m, hm, hrel⟩ :=
    exists_functorLaws_above X c n hc L j N hN e' g hg
  let Lᵢ : J ⥤ BoundedPresentation.Coefficient (X.obj k).unop n := {
    obj := P
    map := m
    map_id x := hrel (.inl x)
    map_comp f h := hrel (.inr ⟨_, _, _, f, h⟩) }
  refine ⟨k, q ≫ r ≫ s, Lᵢ, hP, ⟨?_⟩⟩
  exact NatIso.ofComponents e'' (fun f => hm f)

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
