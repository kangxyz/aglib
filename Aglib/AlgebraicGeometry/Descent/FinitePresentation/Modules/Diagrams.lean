/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Maps
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Objects
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Finite diagrams of finitely presented module sheaves descend

The actual object models, arrows and finitely many functor equations descend
along an actual cofiltered qcqs scheme limit with affine transition maps.
All pullback comparisons use the specified original scheme cone. No
flatness, injectivity or Noetherianity condition is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (F : I ⥤ Scheme.{u})
  [∀ {i j} (q : i ⟶ j), IsAffineHom (F.map q)]
  [∀ i, CompactSpace (F.obj i)] [∀ i, QuasiSeparatedSpace (F.obj i)]
  (c : Cone F) (hc : IsLimit c)

include hc in
private theorem exists_object_models_above {V : Type v} [Finite V]
    (i₀ : I) (L : V → c.pt.Modules) (hL : ∀ v, (L v).IsFinitePresentation) :
    ∃ (i : I) (_ : i ⟶ i₀) (M : V → (F.obj i).Modules),
      (∀ v, (M v).IsFinitePresentation) ∧
      Nonempty (∀ v, (pullback (c.π.app i)).obj (M v) ≅ L v) := by
  classical
  choose j q N hN he using fun v : V => by
    let := hL v
    exact exists_model_above_of_isLimit F c hc i₀ (L v)
  obtain ⟨i, r, g, _⟩ := IsCofiltered.wideCospan q
  let M (v : V) := (pullback (F.map (g v))).obj (N v)
  refine ⟨i, r, M, ?_, ⟨fun v => ?_⟩⟩
  · intro v
    let := hN v
    infer_instance
  · exact ((pullbackConeCompIso F c (g v)).app (N v)).symm ≪≫ (he v).some

include hc in
private theorem exists_finite_homs_above {V P : Type v} [Finite P]
    (src tgt : P → V) (L : V → c.pt.Modules)
    (f : ∀ p, L (src p) ⟶ L (tgt p))
    (i₀ : I) (M₀ : V → (F.obj i₀).Modules)
    (hM₀ : ∀ v, (M₀ v).IsFinitePresentation)
    (e₀ : ∀ v, (pullback (c.π.app i₀)).obj (M₀ v) ≅ L v) :
    ∃ (i : I) (_ : i ⟶ i₀) (M : V → (F.obj i).Modules),
      (∀ v, (M v).IsFinitePresentation) ∧
      ∃ (e : ∀ v, (pullback (c.π.app i)).obj (M v) ≅ L v)
        (g : ∀ p, M (src p) ⟶ M (tgt p)),
        ∀ p, (pullback (c.π.app i)).map (g p) ≫ (e (tgt p)).hom =
          (e (src p)).hom ≫ f p := by
  classical
  let : Fintype P := Fintype.ofFinite P
  have main (s : Finset P) :
      ∃ (i : I) (_ : i ⟶ i₀) (M : V → (F.obj i).Modules),
        (∀ v, (M v).IsFinitePresentation) ∧
        ∃ (e : ∀ v, (pullback (c.π.app i)).obj (M v) ≅ L v)
          (g : ∀ p ∈ s, M (src p) ⟶ M (tgt p)),
          ∀ p hp, (pullback (c.π.app i)).map (g p hp) ≫ (e (tgt p)).hom =
            (e (src p)).hom ≫ f p := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨i₀, 𝟙 _, M₀, hM₀, e₀, fun p hp => by simp at hp, ?_⟩
      intro p hp
      simp at hp
    | @insert a s ha ih =>
      obtain ⟨i, r, M, hM, e, g, hg⟩ := ih
      let : (M (src a)).IsFinitePresentation := hM (src a)
      let : (M (tgt a)).IsFinitePresentation := hM (tgt a)
      let f₀ := (e (src a)).hom ≫ f a ≫ (e (tgt a)).inv
      obtain ⟨j, q, k, hk⟩ := exists_hom_above_of_isLimit F c hc i
        (M (src a)) (M (tgt a)) f₀
      let E := pullback (F.map q)
      let G := pullback (c.π.app j)
      let b := pullbackConeCompIso F c q
      change b.hom.app (M (src a)) ≫ G.map k = f₀ ≫ b.hom.app (M (tgt a)) at hk
      let M' (v : V) := E.obj (M v)
      let e' (v : V) : G.obj (M' v) ≅ L v := (b.app (M v)).symm ≪≫ e v
      let g' (p : P) (hp : p ∈ insert a s) : M' (src p) ⟶ M' (tgt p) :=
        if h : p = a then by subst p; exact k
        else E.map (g p ((Finset.mem_insert.mp hp).resolve_left h))
      refine ⟨j, q ≫ r, M', ?_, e', g', ?_⟩
      · intro v
        let := hM v
        exact finitePresentation_pullback (F.map q) (M v)
      · intro p hp
        by_cases h : p = a
        · subst p
          simp only [g', dite_eq_left rfl]
          apply (cancel_epi (b.hom.app (M (src a)))).mp
          change b.hom.app (M (src a)) ≫
              (G.map k ≫ b.inv.app (M (tgt a)) ≫ (e (tgt a)).hom) =
            b.hom.app (M (src a)) ≫
              (b.inv.app (M (src a)) ≫ (e (src a)).hom ≫ f a)
          simp only [← Category.assoc]
          rw [hk]
          simp [f₀, Category.assoc]
        · simp only [g', dite_eq_right h]
          change G.map (E.map (g p _)) ≫ b.inv.app (M (tgt p)) ≫ (e (tgt p)).hom =
            b.inv.app (M (src p)) ≫ (e (src p)).hom ≫ f p
          have hb := b.inv.naturality (g p ((Finset.mem_insert.mp hp).resolve_left h))
          change G.map (E.map (g p _)) ≫ b.inv.app (M (tgt p)) =
            b.inv.app (M (src p)) ≫ (pullback (c.π.app i)).map (g p _) at hb
          rw [← Category.assoc, hb, Category.assoc, hg]
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

private def equationLeft {R : Scheme.{u}} {J : Type v} [SmallCategory J]
    (M : J → R.Modules) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)) :
    ∀ a : EquationIndex J, M (equationSource a) ⟶ M (equationTarget a)
  | .inl x => g (𝟙 x)
  | .inr ⟨_, _, _, f, h⟩ => g (f ≫ h)

private def equationRight {R : Scheme.{u}} {J : Type v} [SmallCategory J]
    (M : J → R.Modules) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)) :
    ∀ a : EquationIndex J, M (equationSource a) ⟶ M (equationTarget a)
  | .inl x => 𝟙 (M x)
  | .inr ⟨_, _, _, f, h⟩ => g f ≫ g h

private theorem equationLeft_map {R S : Scheme.{u}}
    {J : Type v} [SmallCategory J] (E : R.Modules ⥤ S.Modules)
    (M : J → R.Modules) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y))
    (a : EquationIndex J) :
    E.map (equationLeft M g a) =
      equationLeft (fun x => E.obj (M x)) (fun f => E.map (g f)) a := by
  cases a with
  | inl x => rfl
  | inr a => rcases a with ⟨x, y, z, f, h⟩; rfl

private theorem equationRight_map {R S : Scheme.{u}}
    {J : Type v} [SmallCategory J] (E : R.Modules ⥤ S.Modules)
    (M : J → R.Modules) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y))
    (a : EquationIndex J) :
    E.map (equationRight M g a) =
      equationRight (fun x => E.obj (M x)) (fun f => E.map (g f)) a := by
  cases a with
  | inl x => exact E.map_id _
  | inr a => rcases a with ⟨x, y, z, f, h⟩; exact E.map_comp _ _

private theorem equation_eq_after_map {R S : Scheme.{u}}
    {J : Type v} [SmallCategory J] (D : J ⥤ S.Modules)
    (M : J → R.Modules) (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y))
    (E : R.Modules ⥤ S.Modules) (e : ∀ x, E.obj (M x) ≅ D.obj x)
    (hg : ∀ {x y : J} (f : x ⟶ y), E.map (g f) ≫ (e y).hom = (e x).hom ≫ D.map f)
    (a : EquationIndex J) : E.map (equationLeft M g a) = E.map (equationRight M g a) := by
  cases a with
  | inl x =>
    apply (cancel_mono (e x).hom).mp
    change E.map (g (𝟙 x)) ≫ (e x).hom = E.map (𝟙 (M x)) ≫ (e x).hom
    rw [hg, E.map_id, D.map_id, Category.id_comp, Category.comp_id]
  | inr a =>
    rcases a with ⟨x, y, z, f, h⟩
    apply (cancel_mono (e z).hom).mp
    change E.map (g (f ≫ h)) ≫ (e z).hom = E.map (g f ≫ g h) ≫ (e z).hom
    calc
      _ = (e x).hom ≫ D.map (f ≫ h) := hg _
      _ = (e x).hom ≫ D.map f ≫ D.map h := by rw [D.map_comp]
      _ = (E.map (g f) ≫ (e y).hom) ≫ D.map h := by rw [hg, Category.assoc]
      _ = E.map (g f) ≫ (E.map (g h) ≫ (e z).hom) := by rw [Category.assoc, hg]
      _ = _ := by rw [E.map_comp, Category.assoc]

omit [∀ i, QuasiSeparatedSpace (F.obj i)] in
include hc in
private theorem exists_functor_laws_above {J : Type v} [SmallCategory J] [FinCategory J]
    (D : J ⥤ c.pt.Modules) (i₀ : I) (M₀ : J → (F.obj i₀).Modules)
    (hM₀ : ∀ x, (M₀ x).IsFinitePresentation)
    (e₀ : ∀ x, (pullback (c.π.app i₀)).obj (M₀ x) ≅ D.obj x)
    (g₀ : ∀ {x y : J}, (x ⟶ y) → (M₀ x ⟶ M₀ y))
    (hg₀ : ∀ {x y : J} (f : x ⟶ y),
      (pullback (c.π.app i₀)).map (g₀ f) ≫ (e₀ y).hom =
        (e₀ x).hom ≫ D.map f) :
    ∃ (i : I) (_ : i ⟶ i₀) (M : J → (F.obj i).Modules),
      (∀ x, (M x).IsFinitePresentation) ∧
      ∃ (e : ∀ x, (pullback (c.π.app i)).obj (M x) ≅ D.obj x)
        (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)),
        (∀ {x y : J} (f : x ⟶ y),
          (pullback (c.π.app i)).map (g f) ≫ (e y).hom = (e x).hom ≫ D.map f) ∧
        ∀ a : EquationIndex J, equationLeft M g a = equationRight M g a := by
  classical
  have main (s : Finset (EquationIndex J)) :
      ∃ (i : I) (_ : i ⟶ i₀) (M : J → (F.obj i).Modules),
        (∀ x, (M x).IsFinitePresentation) ∧
        ∃ (e : ∀ x, (pullback (c.π.app i)).obj (M x) ≅ D.obj x)
          (g : ∀ {x y : J}, (x ⟶ y) → (M x ⟶ M y)),
          (∀ {x y : J} (f : x ⟶ y),
            (pullback (c.π.app i)).map (g f) ≫ (e y).hom = (e x).hom ≫ D.map f) ∧
          ∀ a ∈ s, equationLeft M g a = equationRight M g a := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨i₀, 𝟙 _, M₀, hM₀, e₀, g₀, hg₀, fun a ha => by simp at ha⟩
    | @insert a s ha ih =>
      obtain ⟨i, r, M, hM, e, g, hg, hrel⟩ := ih
      let : (M (equationSource a)).IsFinitePresentation := hM _
      let : (M (equationTarget a)).IsFinitePresentation := hM _
      have heq := equation_eq_after_map D M g (pullback (c.π.app i)) e hg a
      obtain ⟨j, q, hq⟩ := exists_hom_equality_above_of_isLimit F c hc i
        (M (equationSource a)) (M (equationTarget a))
        (equationLeft M g a) (equationRight M g a) heq
      let E := pullback (F.map q)
      let G := pullback (c.π.app j)
      let b := pullbackConeCompIso F c q
      let M' (x : J) := E.obj (M x)
      let e' (x : J) : G.obj (M' x) ≅ D.obj x := (b.app (M x)).symm ≪≫ e x
      let g' {x y : J} (f : x ⟶ y) : M' x ⟶ M' y := E.map (g f)
      refine ⟨j, q ≫ r, M', ?_, e', g', ?_, ?_⟩
      · intro x
        let := hM x
        exact finitePresentation_pullback (F.map q) (M x)
      · intro x y f
        change G.map (E.map (g f)) ≫ b.inv.app (M y) ≫ (e y).hom =
          b.inv.app (M x) ≫ (e x).hom ≫ D.map f
        have hb := b.inv.naturality (g f)
        change G.map (E.map (g f)) ≫ b.inv.app (M y) =
          b.inv.app (M x) ≫ (pullback (c.π.app i)).map (g f) at hb
        rw [← Category.assoc, hb, Category.assoc, hg]
      · intro t ht
        change equationLeft (fun x => E.obj (M x)) (fun f => E.map (g f)) t =
          equationRight (fun x => E.obj (M x)) (fun f => E.map (g f)) t
        rw [← equationLeft_map E M g t, ← equationRight_map E M g t]
        rcases Finset.mem_insert.mp ht with h | h
        · subst t
          exact hq
        · exact congrArg E.map (hrel t h)
  obtain ⟨i, q, M, hM, e, g, hg, hrel⟩ := main Finset.univ
  exact ⟨i, q, M, hM, e, g, hg, fun a => hrel a (Finset.mem_univ a)⟩

include hc in
/-- Every actual functor from a finite category to finitely presented modules
on a cofiltered qcqs scheme limit descends to a later stage, with a native
natural isomorphism after the original limit projection pullback. -/
theorem exists_functor_above_of_isLimit {J : Type v} [SmallCategory J] [FinCategory J]
    (i₀ : I) (D : J ⥤ c.pt.Modules)
    (hD : ∀ x, (D.obj x).IsFinitePresentation) :
    ∃ (i : I) (_ : i ⟶ i₀) (Dᵢ : J ⥤ (F.obj i).Modules),
      (∀ x, (Dᵢ.obj x).IsFinitePresentation) ∧
      Nonempty (Dᵢ ⋙ pullback (c.π.app i) ≅ D) := by
  classical
  obtain ⟨i, q, M, hM, ⟨e⟩⟩ := exists_object_models_above F c hc i₀ D.obj hD
  let A := Σ x : J, Σ y : J, x ⟶ y
  obtain ⟨j, r, N, hN, e', g', hg'⟩ := exists_finite_homs_above F c hc
    (fun a : A => a.1) (fun a : A => a.2.1) D.obj
    (fun a : A => D.map a.2.2) i M hM e
  let g {x y : J} (f : x ⟶ y) : N x ⟶ N y := g' ⟨x, y, f⟩
  have hg {x y : J} (f : x ⟶ y) :
      (pullback (c.π.app j)).map (g f) ≫ (e' y).hom =
        (e' x).hom ≫ D.map f := hg' ⟨x, y, f⟩
  obtain ⟨k, s, P, hP, e'', m, hm, hrel⟩ :=
    exists_functor_laws_above F c hc D j N hN e' g hg
  let Dᵢ : J ⥤ (F.obj k).Modules :=
    { obj := P
      map := m
      map_id x := hrel (.inl x)
      map_comp f h := hrel (.inr ⟨_, _, _, f, h⟩) }
  refine ⟨k, s ≫ r ≫ q, Dᵢ, hP, ⟨?_⟩⟩
  exact NatIso.ofComponents e'' (fun f => hm f)

private def isoDiagram {R : Scheme.{u}} {M N : R.Modules} (e : M ≅ N) :
    Codiscrete Bool ⥤ R.Modules := by
  let P (b : Codiscrete Bool) : R.Modules := Bool.rec M N b.as
  let a (b : Codiscrete Bool) : M ≅ P b := match b with
    | ⟨false⟩ => Iso.refl M
    | ⟨true⟩ => e
  exact
    { obj := P
      map {x y} _ := (a x).inv ≫ (a y).hom
      map_id x := by simp
      map_comp f g := by simp [Category.assoc] }

private theorem isoDiagram_hom {R : Scheme.{u}} {M N : R.Modules} (e : M ≅ N) :
    (isoDiagram e).map (Codiscrete.iso (.mk false) (.mk true)).hom = e.hom := by
  simp [isoDiagram]

private theorem isoDiagram_inv {R : Scheme.{u}} {M N : R.Modules} (e : M ≅ N) :
    (isoDiagram e).map (Codiscrete.iso (.mk false) (.mk true)).inv = e.inv := by
  simp [isoDiagram]

include hc in
/-- A specified isomorphism of finitely presented modules descends with BOTH
its original map and its original inverse, using the finite two-object
codiscrete category and the native natural-isomorphism comparison. -/
theorem exists_iso_above_of_isLimit (i₀ : I) (M N : c.pt.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] (e : M ≅ N) :
    ∃ (i : I) (_ : i ⟶ i₀) (P Q : (F.obj i).Modules),
      (P.IsFinitePresentation ∧ Q.IsFinitePresentation) ∧
      ∃ (d : P ≅ Q) (eP : (pullback (c.π.app i)).obj P ≅ M)
        (eQ : (pullback (c.π.app i)).obj Q ≅ N),
        (pullback (c.π.app i)).map d.hom ≫ eQ.hom = eP.hom ≫ e.hom ∧
        (pullback (c.π.app i)).map d.inv ≫ eP.hom = eQ.hom ≫ e.inv := by
  let : Fintype (Codiscrete Bool) := Fintype.ofEquiv Bool codiscreteEquiv.symm
  let : FinCategory (Codiscrete Bool) :=
    { fintypeObj := inferInstance
      fintypeHom _ _ := Fintype.ofFinite _ }
  have hfp : ∀ b : Codiscrete Bool, ((isoDiagram e).obj b).IsFinitePresentation := by
    rintro ⟨b⟩
    cases b
    · exact inferInstanceAs M.IsFinitePresentation
    · exact inferInstanceAs N.IsFinitePresentation
  obtain ⟨i, q, D, hD, ⟨a⟩⟩ := exists_functor_above_of_isLimit F c hc i₀ (isoDiagram e) hfp
  refine ⟨i, q, D.obj (.mk false), D.obj (.mk true), ⟨hD _, hD _⟩,
    D.mapIso (Codiscrete.iso (.mk false) (.mk true)), a.app (.mk false), a.app (.mk true), ?_, ?_⟩
  · simpa only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_hom, Iso.app_hom,
      isoDiagram_hom, isoDiagram, Iso.refl_inv, Category.id_comp] using
      a.hom.naturality (Codiscrete.iso (.mk false) (.mk true)).hom
  · simpa only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_inv, Iso.app_hom,
      isoDiagram_inv, isoDiagram, Iso.refl_hom, Category.comp_id] using
      a.hom.naturality (Codiscrete.iso (.mk false) (.mk true)).inv

include hc in
/-- On a given qcqs scheme model, the actual finite module diagram on its
literal limit base change descends to an actual later canonical base change. -/
theorem exists_functor_above_of_baseChange {J : Type v} [SmallCategory J] [FinCategory J]
    (i₀ : I) {X : Scheme.{u}} (a : X ⟶ F.obj i₀) [QuasiCompact a] [QuasiSeparated a]
    (L : J ⥤ (Limits.pullback (c.π.app i₀) a).Modules)
    (hL : ∀ x, (L.obj x).IsFinitePresentation) :
    ∃ (j : Over i₀) (_ : j ⟶ Over.mk (𝟙 i₀))
      (Lⱼ : J ⥤ ((Scheme.baseChangeDiagram F i₀ a).obj j).Modules),
      (∀ x, (Lⱼ.obj x).IsFinitePresentation) ∧
      Nonempty (Lⱼ ⋙ pullback ((Scheme.baseChangeCone F c i₀ a).π.app j) ≅ L) := by
  exact exists_functor_above_of_isLimit (Scheme.baseChangeDiagram F i₀ a)
    (Scheme.baseChangeCone F c i₀ a) (Scheme.isLimitBaseChangeCone F c hc i₀ a)
    (Over.mk (𝟙 i₀)) L hL

end AlgebraicGeometry.Scheme.Modules
