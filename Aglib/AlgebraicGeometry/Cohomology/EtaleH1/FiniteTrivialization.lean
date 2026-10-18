/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedBaseChange
public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.Topology.Connected.Clopen
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Actual finite local trivializations of represented étale coefficients

Construction prerequisite for finite local trivializations in
`K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The Galois-category representative theorem constructs a finite splitting
cover. Its graph sections are disjoint and cover the pulled-back coefficient
scheme: both statements are proved using the faithful fibre and actual clopen
subschemes. Restriction of global sections is therefore locally bijective on
the small étale site. Sheafification gives the finite constant-sheaf isomorphism,
and the proved represented-sheaf base-change isomorphism supplies the actual
inverse-image trivialization.

The retained inputs are the displayed Galois-category and fibre-functor classes
on the actual finite étale category. Preconnectedness of the base makes the
nonempty splitting cover surjective. No representability, splitting-cover, or
local-constancy premise is supplied. Positive annihilation and invertibility
remain separate explicit conditions in the final finite-coefficient constructor.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite mk toEtale)
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- A finite étale splitting cover with a point at which every coefficient
fibre point extends uniquely to a section over the cover. This records an
intermediate geometric construction, not a local-trivialization premise. -/
structure FiniteSplittingCover (H : Grp (Over X)) where
  /-- The finite etale splitting cover of `X`. -/
  cover : Scheme.FiniteEtale X
  /-- The chosen point of the splitting cover above `s`. -/
  point : Over.mk s ⟶ cover.obj
  galois : PreGaloisCategory.IsGalois cover
  evaluation_bijective : Function.Bijective (fun p : cover.obj ⟶ H.X => point ≫ p)

/-- The actual Galois-category representative theorem constructs the finite
étale splitting cover. No splitting or comparison premise is supplied. -/
def finiteSplittingCover (H : Grp (Over X)) [IsFinite H.X.hom] [Etale H.X.hom] :
    FiniteSplittingCover s H := by
  apply Classical.choice
  let HC : Scheme.FiniteEtale X := ⟨H.X, inferInstance, inferInstance⟩
  obtain ⟨T, a, hT, hbij⟩ := PreGaloisCategory.exists_galois_representative (fiberToFinite s) HC
  refine ⟨⟨T, a, hT, ?_⟩⟩
  let e : (T.obj ⟶ H.X) ≃ (T ⟶ HC) :=
    { toFun := fun p => (ObjectProperty.homMk p : T ⟶ HC)
      invFun := fun q => q.hom
      left_inv := fun _ => rfl
      right_inv := fun p => by cases p; rfl }
  exact hbij.comp e.bijective

variable {s}

/-- Evaluation of sections preserves the actual additive group structure. -/
-- Keep the original commutative coefficient-group input of the additive evaluation interface.
@[nolint unusedArguments]
def FiniteSplittingCover.evaluation {H : Grp (Over X)} [IsCommMonObj H.X]
    (T : FiniteSplittingCover s H) :
    Additive (T.cover.obj ⟶ H.X) ≃+ Additive (Over.mk s ⟶ H.X) :=
  AddEquiv.ofBijective
    ({ toFun := fun p => Additive.ofMul (T.point ≫ p.toMul)
       map_zero' := congrArg Additive.ofMul (MonObj.comp_one T.point)
       map_add' := fun p q => congrArg Additive.ofMul (MonObj.comp_mul T.point p.toMul q.toMul) } :
      Additive (T.cover.obj ⟶ H.X) →+ Additive (Over.mk s ⟶ H.X))
    ((Additive.ofMul.bijective.comp T.evaluation_bijective).comp Additive.toMul.bijective)

omit [PreGaloisCategory.FiberFunctor (fiberToFinite s)] in
/-- The splitting cover has finitely many coefficient sections, unlike an
arbitrary test scheme on the small étale site. -/
-- Keep the original etale coefficient-group hypothesis of the splitting-cover interface.
@[nolint unusedArguments]
theorem FiniteSplittingCover.finite_sections {H : Grp (Over X)}
    [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    (T : FiniteSplittingCover s H) : Finite (Additive (T.cover.obj ⟶ H.X)) := by
  let : Finite (Over.mk s ⟶ H.X) := _root_.AlgebraicGeometry.Scheme.Finite.finite_hom_over_point
    H.X.hom s
  exact Finite.of_equiv (Additive (Over.mk s ⟶ H.X)) T.evaluation.symm.toEquiv

omit [PreGaloisCategory.FiberFunctor (fiberToFinite s)] in
/-- Over a preconnected base, the actual nonempty finite étale splitting
cover is topologically surjective, so it is a genuine small-étale cover. -/
theorem FiniteSplittingCover.surjective {H : Grp (Over X)}
    (T : FiniteSplittingCover s H) [PreconnectedSpace X] :
    Function.Surjective T.cover.obj.hom := by
  have hcl : IsClopen (Set.range T.cover.obj.hom) :=
    ⟨T.cover.obj.hom.isClosedMap.isClosed_range, T.cover.obj.hom.isOpenMap.isOpen_range⟩
  let k : Spec (CommRingCat.of K) := ⟨⊥, inferInstance⟩
  have hne : (Set.range T.cover.obj.hom).Nonempty :=
    ⟨T.cover.obj.hom (T.point.left k), ⟨T.point.left k, rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Every point in the chosen fibre of the Galois splitting cover, not just
the selected one, evaluates coefficient sections bijectively. -/
theorem FiniteSplittingCover.evaluation_bijective_at {H : Grp (Over X)}
    (T : FiniteSplittingCover s H) (b : Over.mk s ⟶ T.cover.obj) :
    Function.Bijective (fun p : T.cover.obj ⟶ H.X => b ≫ p) := by
  let := T.galois
  let g : Aut T.cover :=
    (PreGaloisCategory.evaluationEquivOfIsGalois (fiberToFinite s) T.cover T.point).symm b
  have hb : T.point ≫ g.hom.hom = b :=
    (PreGaloisCategory.evaluationEquivOfIsGalois (fiberToFinite s) T.cover
      T.point).apply_symm_apply b
  let e : (T.cover.obj ⟶ H.X) ≃ (T.cover.obj ⟶ H.X) :=
    Iso.homCongr ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X).mapIso g).symm
      (Iso.refl H.X)
  have h := T.evaluation_bijective.comp e.bijective
  change Function.Bijective (fun p => T.point ≫ (g.hom.hom ≫ p ≫ 𝟙 H.X)) at h
  simpa only [Category.comp_id, ← Category.assoc, hb] using h

open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.FiniteEtale.Connectedness

/-- A finite family of finite étale maps covering the faithful fibre covers
all scheme points. The proof uses the actual clopen complement. -/
theorem jointly_surjective_of_fiber {I : Type*} [Finite I]
    {Y : Scheme.FiniteEtale X} {Z : I → Scheme.FiniteEtale X} (f : ∀ i, Z i ⟶ Y)
    (h : ∀ p : Over.mk s ⟶ Y.obj, ∃ i, ∃ q : Over.mk s ⟶ (Z i).obj,
      q ≫ (f i).hom = p) :
    ∀ y : Y.obj.left, ∃ i, ∃ z : (Z i).obj.left, (f i).hom.left z = y := by
  let V : Set Y.obj.left := ⋃ i, Set.range (f i).hom.left
  have hV : IsClopen V := ⟨isClosed_iUnion_of_finite (fun i => (hom_range_isClopen (f i)).1),
    isOpen_iUnion (fun i => (hom_range_isClopen (f i)).2)⟩
  let U : Y.obj.left.Opens := ⟨Vᶜ, hV.1.isOpen_compl⟩
  let C := clopenCover Y U hV.2.isClosed_compl
  let j : C ⟶ Y := clopenCoverι Y U hV.2.isClosed_compl
  have he : IsEmpty ((fiberToFinite s).obj C) := by
    refine ⟨fun (p : Over.mk s ⟶ C.obj) => ?_⟩
    obtain ⟨i, q, hq⟩ := h (p ≫ j.hom)
    let k : Spec (CommRingCat.of K) := ⟨⊥, inferInstance⟩
    have hp := (p.left k).property
    apply hp
    change j.hom.left (p.left k) ∈ V
    exact Set.mem_iUnion.mpr ⟨i, q.left k,
      congrArg (fun a : Over.mk s ⟶ Y.obj => a.left k) hq⟩
  have hc : IsEmpty C.obj.left :=
    (Scheme.FiniteEtale.Connectedness.isInitial_iff_isEmpty C).mp
      ((PreGaloisCategory.initial_iff_fiber_empty
      (fiberToFinite s) C).mpr he)
  intro y
  by_contra hn
  have hy : y ∉ V := by simpa only [V, Set.mem_iUnion, Set.mem_range] using hn
  exact hc.false (⟨y, hy⟩ : U)

/-- Disjointness in the faithful fibre implies disjointness of actual scheme
images, by applying the fibre functor to the scheme kernel pair. -/
theorem disjoint_ranges_of_fiber {Y Z W : Scheme.FiniteEtale X} (f : Y ⟶ W) (g : Z ⟶ W)
    (h : ∀ p : Over.mk s ⟶ Y.obj, ∀ q : Over.mk s ⟶ Z.obj,
      p ≫ f.hom ≠ q ≫ g.hom) :
    Disjoint (Set.range f.hom.left) (Set.range g.hom.left) := by
  let := hom_isFinite f
  let := hom_isFinite g
  let := hom_etale f
  let := hom_etale g
  let C : Scheme.FiniteEtale X :=
    Scheme.FiniteEtale.mk (pullback.fst f.hom.left g.hom.left ≫ Y.obj.hom)
  let a : C ⟶ Y := ObjectProperty.homMk (Over.homMk (pullback.fst _ _) rfl)
  let b : C ⟶ Z := ObjectProperty.homMk (Over.homMk (pullback.snd _ _) (by
    change pullback.snd f.hom.left g.hom.left ≫ Z.obj.hom =
      pullback.fst f.hom.left g.hom.left ≫ Y.obj.hom
    rw [← Over.w f.hom, ← Over.w g.hom]
    simp only [← Category.assoc, pullback.condition]))
  have he : IsEmpty ((fiberToFinite s).obj C) := by
    refine ⟨fun (p : Over.mk s ⟶ C.obj) => h (p ≫ a.hom) (p ≫ b.hom) ?_⟩
    apply Over.OverMorphism.ext
    change (p.left ≫ pullback.fst _ _) ≫ f.hom.left =
      (p.left ≫ pullback.snd _ _) ≫ g.hom.left
    simp only [Category.assoc, pullback.condition]
  exact Scheme.isEmpty_pullback_iff.mp ((Scheme.FiniteEtale.Connectedness.isInitial_iff_isEmpty
    C).mp
    ((PreGaloisCategory.initial_iff_fiber_empty (fiberToFinite s) C).mpr he))

namespace FiniteSplittingCover
variable {H : Grp (Over X)} [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
variable (T : FiniteSplittingCover s H)

/-- The coefficient scheme after base change, still viewed as a finite cover of X. -/
abbrev splitCover : Scheme.FiniteEtale X :=
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk (pullback.snd H.X.hom T.cover.obj.hom
    ≫ T.cover.obj.hom)

/-- A section of the original coefficient over the splitting cover has its
actual graph in the scheme-theoretic base change. -/
def graph (q : T.cover.obj ⟶ H.X) : T.cover ⟶ T.splitCover :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift q.left (𝟙 _) (by simp)) (by simp))

/-- The second pullback projection from the split coefficient cover to the splitting cover. -/
def projection : T.splitCover ⟶ T.cover :=
  ObjectProperty.homMk (Over.homMk (pullback.snd _ _) rfl)

/-- The first pullback projection from the split coefficient cover to the coefficient scheme. -/
def coefficientProjection : T.splitCover ⟶ _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk H.X.hom :=
  ObjectProperty.homMk (Over.homMk (pullback.fst _ _) pullback.condition)

omit [PreGaloisCategory.FiberFunctor (fiberToFinite s)] [IsCommMonObj H.X] in
@[simp] theorem graph_projection (q : T.cover.obj ⟶ H.X) :
    T.graph q ≫ T.projection = 𝟙 T.cover := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp [graph, projection]

omit [PreGaloisCategory.FiberFunctor (fiberToFinite s)] [IsCommMonObj H.X] in
@[simp] theorem graph_coefficientProjection (q : T.cover.obj ⟶ H.X) :
    (T.graph q).hom ≫ T.coefficientProjection.hom = q := by
  apply Over.OverMorphism.ext
  simp [graph, coefficientProjection]

instance graph_mono (q : T.cover.obj ⟶ H.X) : Mono (T.graph q) where
  right_cancellation f g h := by
    have := congrArg (fun a => a ≫ T.projection) h
    simpa only [Category.assoc, graph_projection, Category.comp_id] using this

instance graph_isOpenImmersion (q : T.cover.obj ⟶ H.X) :
    IsOpenImmersion (T.graph q).hom.left := isOpenImmersion_of_mono _

/-- The finitely many graph sections cover the actual pulled-back coefficient
scheme, at every scheme point. -/
theorem graphs_cover : ∀ y : T.splitCover.obj.left,
    ∃ q : T.cover.obj ⟶ H.X, ∃ z : T.cover.obj.left, (T.graph q).hom.left z = y := by
  let : Finite (Additive (T.cover.obj ⟶ H.X)) := T.finite_sections
  let : Finite (T.cover.obj ⟶ H.X) := Finite.of_equiv _ Additive.toMul
  apply jointly_surjective_of_fiber (s := s) T.graph
  intro p
  let b := p ≫ T.projection.hom
  obtain ⟨q, hq⟩ := (T.evaluation_bijective_at b).surjective
    (p ≫ T.coefficientProjection.hom)
  refine ⟨q, b, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change b.left ≫ (T.graph q).hom.left ≫ pullback.fst _ _ = p.left ≫ pullback.fst _ _
    simpa only [graph, coefficientProjection, ObjectProperty.homMk_hom, Over.homMk_left,
      Over.comp_left,
      pullback.lift_fst, Category.assoc] using congrArg (fun a => a.left) hq
  · change b.left ≫ (T.graph q).hom.left ≫ pullback.snd _ _ = p.left ≫ pullback.snd _ _
    simp [graph, b, projection]

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Distinct global coefficient sections have disjoint graph images. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem graphs_disjoint {q r : T.cover.obj ⟶ H.X} (hqr : q ≠ r) :
    Disjoint (Set.range (T.graph q).hom.left) (Set.range (T.graph r).hom.left) := by
  apply disjoint_ranges_of_fiber (s := s)
  intro a b hab
  have hab' : a = b := by
    have e := congrArg (fun f => f ≫ T.projection.hom) hab
    simpa only [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      graph_projection, ObjectProperty.FullSubcategory.id_hom, Category.comp_id] using e
  subst b
  have e := congrArg (fun f => f ≫ T.coefficientProjection.hom) hab
  have eqv : a ≫ q = a ≫ r := by
    simpa only [Category.assoc, graph_coefficientProjection] using e
  exact hqr ((T.evaluation_bijective_at a).injective eqv)

/-- The actual commutative coefficient group after pullback to the splitting cover. -/
abbrev localGroup : Grp (Over T.cover.obj.left) := baseChangedGroup T.cover.obj.hom H

/-- Global sections of the pulled-back group are exactly the coefficient
sections over the splitting cover. -/
def sectionEquiv : (T.cover.obj ⟶ H.X) ≃
    (Over.mk (𝟙 T.cover.obj.left) ⟶ T.localGroup.X) where
  toFun q := Over.homMk (T.graph q).hom.left (by simp [graph])
  invFun q := Over.homMk (q.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (q.left ≫ T.localGroup.X.hom) ≫ T.cover.obj.hom = T.cover.obj.hom
    rw [Over.w q]
    simp)
  left_inv q := by
    apply Over.OverMorphism.ext
    simp [graph]
  right_inv q := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [graph]
    · change (T.graph _).hom.left ≫ pullback.snd _ _ = q.left ≫ T.localGroup.X.hom
      rw [Over.w q]
      simp [graph]

/-- The finite additive value of the constant sheaf in the trivialization. -/
abbrev localValue : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (RepresentedSections T.localGroup (Over.mk (𝟙 T.cover.obj.left)))

instance finite_localValue : Finite T.localValue := by
  let : Finite (Additive (T.cover.obj ⟶ H.X)) := T.finite_sections
  let : Finite (T.cover.obj ⟶ H.X) := Finite.of_equiv _ Additive.toMul
  let : Finite (Over.mk (𝟙 T.cover.obj.left) ⟶ T.localGroup.X) :=
    Finite.of_equiv _ T.sectionEquiv
  infer_instance

/-- The structural map to the terminal test scheme. -/
def terminalMap (U : T.cover.obj.left.Etale) :
    (Scheme.Etale.forget _).obj U ⟶ Over.mk (𝟙 T.cover.obj.left) :=
  Over.homMk U.hom (by simp)

/-- The canonical map from constant global sections to the represented
presheaf restricts each section along the structural morphism. -/
def constantSectionMap :
    (Functor.const T.cover.obj.left.Etaleᵒᵖ).obj T.localValue ⟶
      representedPresheaf T.localGroup where
  app U := AddCommGrpCat.ofHom (representedSectionsPullback T.localGroup
    (T.terminalMap U.unop))
  naturality {U V} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro q
    apply ULift.ext
    apply congrArg Additive.ofMul
    change (T.terminalMap V.unop ≫ q.down.toMul) =
      (Scheme.Etale.forget _).map f.unop ≫ (T.terminalMap U.unop ≫ q.down.toMul)
    rw [← Category.assoc]
    apply congrArg (fun a => a ≫ q.down.toMul)
    apply Over.OverMorphism.ext
    exact (MorphismProperty.Over.w f.unop).symm

/-- Restriction of global sections is injective on every nonempty test scheme:
distinct graph sections have disjoint images. -/
theorem constantSectionMap_injective (U : T.cover.obj.left.Etale) (x : U.left) :
    Function.Injective (T.constantSectionMap.app (op U)) := by
  intro q r h
  let q₀ := T.sectionEquiv.symm q.down.toMul
  let r₀ := T.sectionEquiv.symm r.down.toMul
  have hq : (T.graph q₀).hom.left = q.down.toMul.left :=
    congrArg (fun a => a.left) (T.sectionEquiv.apply_symm_apply q.down.toMul)
  have hr : (T.graph r₀).hom.left = r.down.toMul.left :=
    congrArg (fun a => a.left) (T.sectionEquiv.apply_symm_apply r.down.toMul)
  have he := congrArg (fun a => a.down.toMul.left x) h
  change q.down.toMul.left (U.hom x) = r.down.toMul.left (U.hom x) at he
  have eq₀ : q₀ = r₀ := by
    by_contra hn
    apply Set.disjoint_left.mp (T.graphs_disjoint hn)
      (show q.down.toMul.left (U.hom x) ∈ Set.range (T.graph q₀).hom.left from
        ⟨U.hom x, congrArg (fun a => a (U.hom x)) hq⟩)
    exact ⟨U.hom x, (congrArg (fun a => a (U.hom x)) hr).trans he.symm⟩
  apply ULift.ext
  apply Additive.toMul.injective
  exact T.sectionEquiv.symm.injective eq₀

instance constantSectionMap_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology T.cover.obj.left)
      T.constantSectionMap where
  equalizerSieve_mem {U} q r h := by
    change _ ∈ (T.cover.obj.left.smallGrothendieckTopology @Etale) U.unop
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro x
    refine ⟨U.unop, 𝟙 _, x, ?_, inferInstanceAs (Etale (𝟙 _)), rfl⟩
    change q = r
    exact T.constantSectionMap_injective U.unop x h

/-- Every coefficient section becomes a global splitting section on an actual
étale neighbourhood. The neighbourhood is a pullback of a graph section. -/
instance constantSectionMap_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology T.cover.obj.left)
      T.constantSectionMap where
  imageSieve_mem {U} t := by
    change _ ∈ (T.cover.obj.left.smallGrothendieckTopology @Etale) U
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro x
    obtain ⟨q, z, hz⟩ := T.graphs_cover (t.down.toMul.left x)
    let g := (T.graph q).hom.left
    let a := t.down.toMul.left
    have hg : IsOpenImmersion g := T.graph_isOpenImmersion q
    let V : T.cover.obj.left.Etale := Scheme.Etale.mk (pullback.snd g a ≫ U.hom)
    let f : V ⟶ U := MorphismProperty.Over.homMk (pullback.snd g a) rfl (by trivial)
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    refine ⟨V, f, y, ?_, inferInstanceAs (Etale (pullback.snd g a)), hy₂⟩
    refine ⟨ULift.up (Additive.ofMul (T.sectionEquiv q)), ?_⟩
    have hcomp : pullback.fst g a = pullback.snd g a ≫ U.hom := by
      have e := congrArg (fun b => b ≫ T.localGroup.X.hom) (pullback.condition (f := g) (g := a))
      have hq : g ≫ T.localGroup.X.hom = 𝟙 _ := (T.sectionEquiv q).w
      have ht : a ≫ T.localGroup.X.hom = U.hom := t.down.toMul.w
      simpa only [Category.assoc, hq, ht, Category.comp_id] using e
    apply ULift.ext
    apply congrArg Additive.ofMul
    apply Over.OverMorphism.ext
    change (pullback.snd g a ≫ U.hom) ≫ g = pullback.snd g a ≫ a
    rw [← hcomp]
    exact pullback.condition

/-- The actual constant sheaf comparison, proved by local bijectivity of the
canonical section map. No local-trivialization premise is assumed. -/
def constantSheafIso :
    (constantSheaf (Scheme.smallEtaleTopology T.cover.obj.left) AddCommGrpCat.{u + 1}).obj
      T.localValue ≅ representedSheaf T.localGroup := by
  let := hasSheafifyLarge T.cover.obj.left
  have hiso : IsIso ((presheafToSheaf (Scheme.smallEtaleTopology T.cover.obj.left)
      AddCommGrpCat.{u + 1}).map T.constantSectionMap) :=
    (GrothendieckTopology.W_iff _ _).mp
      (GrothendieckTopology.W_of_isLocallyBijective _ T.constantSectionMap)
  exact asIso ((presheafToSheaf (Scheme.smallEtaleTopology T.cover.obj.left)
    AddCommGrpCat.{u + 1}).map T.constantSectionMap) ≪≫
      (sheafificationIso (representedSheaf T.localGroup)).symm

/-- The represented coefficient sheaf becomes the finite constant sheaf after
actual scheme inverse image along the constructed splitting cover. -/
def localTrivializationIso :
    (inverseImage T.cover.obj.hom).obj (representedSheaf H) ≅
      (constantSheaf (Scheme.smallEtaleTopology T.cover.obj.left) AddCommGrpCat.{u + 1}).obj
        T.localValue :=
  representedSheafBaseChangeIso T.cover.obj.hom H ≪≫ T.constantSheafIso.symm

/-- The constructed splitting cover is a one-chart finite local
trivialization in the actual small-étale definition. -/
def finiteLocalTrivialization [PreconnectedSpace X] :
    FiniteLocalTrivialization (representedSheaf H) where
  index := PUnit.{u + 1}
  chart _ := (toEtale X).obj T.cover
  covers x := by
    obtain ⟨y, hy⟩ := T.surjective x
    exact ⟨PUnit.unit, y, hy⟩
  value _ := T.localValue
  finite_value _ := T.finite_localValue
  trivialization _ := T.localTrivializationIso

end FiniteSplittingCover

include s

/-- A finite commutative étale group scheme represents a finite locally
constant additive sheaf. Only the displayed actual GC/FF classes and
preconnectedness of the base are retained. -/
theorem representedSheaf_isFiniteLocallyConstant (H : Grp (Over X))
    [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom] [PreconnectedSpace X] :
    IsFiniteLocallyConstant (representedSheaf H) :=
  ⟨(finiteSplittingCover s H).finiteLocalTrivialization⟩

/-- In particular, every finite continuous additive module gives an actual
finite locally constant represented coefficient sheaf. -/
theorem moduleSheaf_isFiniteLocallyConstant
    (M : Type*) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (Scheme.EtaleFundamentalGroups.FiberAutGroup s) M]
    [ContinuousSMul (Scheme.EtaleFundamentalGroups.FiberAutGroup s) M]
    [PreconnectedSpace X] : IsFiniteLocallyConstant (moduleSheaf s M) :=
  representedSheaf_isFiniteLocallyConstant (s := s) _

/-- The finite locally constant, positive prime-to-residue-characteristic
coefficient package is constructed from the finite module's actual annihilator
and the displayed invertibility condition on X. -/
def moduleFiniteCoefficient
    (M : Type*) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (Scheme.EtaleFundamentalGroups.FiberAutGroup s) M]
    [ContinuousSMul (Scheme.EtaleFundamentalGroups.FiberAutGroup s) M]
    [PreconnectedSpace X] (n : ℕ) (hn : 0 < n) (hM : ∀ m : M, n • m = 0)
    (hX : LevelInvertible X n) : FiniteCoefficient (moduleSheaf s M) where
  level := n
  positive := hn
  killed := moduleSheaf_killedBy s M n hM
  invertible := hX
  locally_constant := moduleSheaf_isFiniteLocallyConstant (s := s) M

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 4c05b1090dc6dee280c006d92ebdb77f155b6652e1e3672712aaabbb423c7733.
Definitions, hypotheses and universes are retained modulo native names. -/
