/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Fiber
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.Topology.Connected.Clopen

/-!
# Connected finite étale schemes and transitive geometric fibres

This is the connected-cover bridge for the primitive-character construction in
`K2-018#prop:k2018-arithmetic-characters`, on manuscript source basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982` (essay source basis
`ac804cb2f648f42380e612235b972786506d0b9f`). The actual finite étale category and
point-valued fibre are those of `FiniteEtaleCovers.lean`, accepted SHA256
`593e6b847bd845fa2b13de95a7c0b7991a2cf94b70d27a14ca1d24b5833adaa6`.

For every base scheme, the underlying scheme of an actual finite étale cover is
connected exactly when the cover is connected in the categorical sense. Every
arrow between such covers is finite étale. Its actual scheme kernel pair is
again a finite étale cover, so categorical monicity implies scheme monicity.
Finite étale monomorphisms are open immersions with closed image. Conversely,
a clopen subscheme is itself a finite étale subcover. The empty scheme identifies
the categorical initial objects with the covers having empty underlying space.
No comparison of categorical and topological connectedness is assumed.

For the natural action on the actual point-valued fibre, the only retained
standard inputs are `[GaloisCategory (Cover B)]` and
`[PreGaloisCategory.FiberFunctor (fiberToFinite s)]`. The resulting criterion
explicitly requires a nonempty fibre: pretransitivity alone holds vacuously on
the empty fibre. Neither a connected-base hypothesis nor an algebraically
closed point field is added; the fibre-functor class remains an explicit input.
Applying the criterion after geometric base change still requires the relevant
standard classes and the transitivity argument on that base-changed fibre.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite forget forgetToScheme mk)

namespace AlgebraicGeometry.Scheme.FiniteEtale.Connectedness
universe u
variable {B : Scheme.{u}}

/-- Every morphism between finite étale covers is finite as a scheme morphism. -/
theorem hom_isFinite {Y Z : Scheme.FiniteEtale B} (f : Y ⟶ Z) : IsFinite f.hom.left := by
  have : IsFinite (f.hom.left ≫ Z.obj.hom) := by rw [Over.w]; infer_instance
  exact IsFinite.of_comp f.hom.left Z.obj.hom

/-- Every morphism between finite étale covers is étale as a scheme morphism. -/
theorem hom_etale {Y Z : Scheme.FiniteEtale B} (f : Y ⟶ Z) : Etale f.hom.left := by
  have : Etale (f.hom.left ≫ Z.obj.hom) := by rw [Over.w]; infer_instance
  exact Etale.of_comp f.hom.left Z.obj.hom

attribute [local instance] hom_isFinite hom_etale

/-- Categorical monicity is physical scheme monicity. The actual scheme kernel
pair supplies the two test morphisms inside the finite étale category. -/
theorem mono_left {Y Z : Scheme.FiniteEtale B} (i : Z ⟶ Y) [Mono i] : Mono i.hom.left := by
  let P : Scheme.FiniteEtale B := mk (pullback.fst i.hom.left i.hom.left ≫ Z.obj.hom)
  let a : P ⟶ Z := ObjectProperty.homMk (Over.homMk
    (pullback.fst i.hom.left i.hom.left) rfl)
  let b : P ⟶ Z := ObjectProperty.homMk (Over.homMk
    (pullback.snd i.hom.left i.hom.left) (by
      change pullback.snd i.hom.left i.hom.left ≫ Z.obj.hom =
        pullback.fst i.hom.left i.hom.left ≫ Z.obj.hom
      rw [← Over.w i.hom]
      simp only [← Category.assoc, pullback.condition]))
  have hab : a = b := (cancel_mono i).mp (by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact pullback.condition)
  have hfst : pullback.fst i.hom.left i.hom.left =
      pullback.snd i.hom.left i.hom.left := congrArg (fun f : P ⟶ Z => f.hom.left) hab
  constructor
  intro T f g hfg
  have h := congrArg (fun p => pullback.lift f g hfg ≫ p) hfst
  simpa only [pullback.lift_fst, pullback.lift_snd] using h

/-- The empty scheme, with its unique structural map, as a finite étale cover. -/
abbrev emptyCover (B : Scheme.{u}) : Scheme.FiniteEtale B := mk (Scheme.emptyTo B)

/-- A cover with empty underlying space is categorically initial. -/
def isInitialCoverOfIsEmpty (Y : Scheme.FiniteEtale B) [IsEmpty Y.obj.left] : IsInitial Y :=
  .ofUniqueHom
    (fun Z => ObjectProperty.homMk (Over.homMk (isInitialOfIsEmpty.to Z.obj.left)
      (isInitialOfIsEmpty.hom_ext _ _)))
    (fun Z f => by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact isInitialOfIsEmpty.hom_ext _ _)

/-- Initial objects of the actual finite étale category are exactly empty schemes. -/
theorem isInitial_iff_isEmpty (Y : Scheme.FiniteEtale B) :
    Nonempty (IsInitial Y) ↔ IsEmpty Y.obj.left := by
  constructor
  · rintro ⟨h⟩
    let f : Y.obj.left ⟶ (∅ : Scheme.{u}) := (h.to (emptyCover B)).hom.left
    exact ⟨fun y => isEmptyElim (f y)⟩
  · intro h
    let := h
    exact ⟨isInitialCoverOfIsEmpty Y⟩

/-- Noninitiality of an actual finite étale cover is topological nonemptiness. -/
theorem not_initial_iff_nonempty (Y : Scheme.FiniteEtale B) :
    (IsInitial Y → False) ↔ Nonempty Y.obj.left := by
  rw [← not_isEmpty_iff]
  constructor
  · intro h hE
    let := hE
    exact h (isInitialCoverOfIsEmpty Y)
  · intro h hi
    exact h ((isInitial_iff_isEmpty Y).mp ⟨hi⟩)

/-- Restrict a finite étale cover to an open and closed subscheme. -/
def clopenCover (Y : Scheme.FiniteEtale B) (U : Y.obj.left.Opens)
    (hU : IsClosed (U : Set Y.obj.left)) :
    Scheme.FiniteEtale B := by
  let : IsClosedImmersion U.ι := .of_isPreimmersion U.ι (by rwa [Scheme.Opens.range_ι])
  exact mk (U.ι ≫ Y.obj.hom)

/-- The inclusion of the actual clopen subcover. -/
def clopenCoverι (Y : Scheme.FiniteEtale B) (U : Y.obj.left.Opens)
    (hU : IsClosed (U : Set Y.obj.left)) :
    clopenCover Y U hU ⟶ Y := ObjectProperty.homMk (Over.homMk U.ι rfl)

/-- A categorically connected actual finite étale cover has connected underlying
space: every nonempty clopen restriction is an isomorphism. -/
theorem connectedSpace_of_categoricalConnected (Y : Scheme.FiniteEtale B)
    [PreGaloisCategory.IsConnected Y] : ConnectedSpace Y.obj.left := by
  apply connectedSpace_iff_clopen.mpr
  refine ⟨(not_initial_iff_nonempty Y).mp PreGaloisCategory.IsConnected.notInitial, ?_⟩
  intro V hV
  by_cases h : V = ∅
  · exact Or.inl h
  right
  let U : Y.obj.left.Opens := ⟨V, hV.2⟩
  let Z := clopenCover Y U hV.1
  let i : Z ⟶ Y := clopenCoverι Y U hV.1
  have : Mono i := (forgetToScheme B).mono_of_mono_map (by
    change Mono U.ι
    infer_instance)
  have hz : IsInitial Z → False := (not_initial_iff_nonempty Z).mpr (by
    change Nonempty (U : Scheme)
    exact (Set.nonempty_iff_ne_empty.mpr h).to_subtype)
  have : IsIso i := PreGaloisCategory.IsConnected.noTrivialComponent Z i hz
  have : IsIso U.ι := by
    change IsIso ((forgetToScheme B).map i)
    infer_instance
  have hr := Set.range_eq_univ.mpr U.ι.surjective
  rw [Scheme.Opens.range_ι] at hr
  exact hr

/-- Every morphism between finite étale covers has open and closed image. -/
theorem hom_range_isClopen {Y Z : Scheme.FiniteEtale B} (i : Z ⟶ Y) :
    IsClopen (Set.range i.hom.left) :=
  ⟨i.hom.left.isClosedMap.isClosed_range, i.hom.left.isOpenMap.isOpen_range⟩

/-- A subobject in the finite étale category is an actual open immersion. -/
theorem isOpenImmersion_of_mono {Y Z : Scheme.FiniteEtale B} (i : Z ⟶ Y) [Mono i] :
    IsOpenImmersion i.hom.left := by
  let := mono_left i
  exact IsOpenImmersion.of_flat_of_mono i.hom.left

/-- An actual connected finite étale scheme has no proper nonempty subcover. -/
theorem categoricalConnected_of_connectedSpace (Y : Scheme.FiniteEtale B)
    [ConnectedSpace Y.obj.left] :
    PreGaloisCategory.IsConnected Y where
  notInitial := (not_initial_iff_nonempty Y).mpr inferInstance
  noTrivialComponent Z i hi hZ := by
    let := hi
    let := mono_left i
    have : Nonempty Z.obj.left := (not_initial_iff_nonempty Z).mp hZ
    have hr : Set.range i.hom.left = Set.univ :=
      (hom_range_isClopen i).eq_univ (Set.range_nonempty _)
    have : Surjective i.hom.left := ⟨Set.range_eq_univ.mp hr⟩
    have : IsIso i.hom.left := Flat.isIso_of_surjective_of_mono i.hom.left
    have : IsIso ((Over.forget B).map i.hom) := by
      change IsIso i.hom.left
      infer_instance
    have : IsIso ((forget B).map i) := by
      change IsIso i.hom
      exact isIso_of_reflects_iso i.hom (Over.forget B)
    exact isIso_of_reflects_iso i (forget B)

/-- Scheme connectedness equals categorical connectedness, over any base scheme. -/
theorem connectedSpace_iff_categoricalConnected (Y : Scheme.FiniteEtale B) :
    ConnectedSpace Y.obj.left ↔ PreGaloisCategory.IsConnected Y := by
  constructor
  · intro h
    let := h
    exact categoricalConnected_of_connectedSpace Y
  · intro h
    let := h
    exact connectedSpace_of_categoricalConnected Y

section Action
variable {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- Under the standard Galois-category and fibre-functor classes, a cover is
categorically connected exactly when its natural fibre action is nonempty and
pretransitive. -/
theorem categoricalConnected_iff_transitive (Y : Scheme.FiniteEtale B) :
    PreGaloisCategory.IsConnected Y ↔
      Nonempty ((fiberToFinite s).obj Y) ∧
      MulAction.IsPretransitive (Aut (fiberToFinite s)) ((fiberToFinite s).obj Y) := by
  constructor
  · intro h
    let := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hne, htrans⟩
    let := hne
    let := htrans
    refine ⟨(PreGaloisCategory.not_initial_iff_fiber_nonempty (fiberToFinite s) Y).mpr hne,
      fun Z i hi hZ => ?_⟩
    let := hi
    obtain ⟨z⟩ := (PreGaloisCategory.not_initial_iff_fiber_nonempty (fiberToFinite s) Z).mp hZ
    have hinj := ConcreteCategory.injective_of_mono_of_preservesPullback ((fiberToFinite s).map i)
    have hsurj : Function.Surjective ((fiberToFinite s).map i) := by
      intro y
      obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
        (M := Aut (fiberToFinite s)) ((fiberToFinite s).map i z) y
      refine ⟨g • z, ?_⟩
      rw [← PreGaloisCategory.mulAction_naturality, hg]
    have : IsIso ((fiberToFinite s).map i) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso i (fiberToFinite s)
/-- Actual scheme connectedness is equivalent to nonemptiness and transitivity
of the canonical natural-fibre action, under the retained standard classes. -/
theorem connectedSpace_iff_transitive (Y : Scheme.FiniteEtale B) :
    ConnectedSpace Y.obj.left ↔
      Nonempty ((fiberToFinite s).obj Y) ∧
      MulAction.IsPretransitive (Aut (fiberToFinite s)) ((fiberToFinite s).obj Y) :=
  (connectedSpace_iff_categoricalConnected Y).trans (categoricalConnected_iff_transitive s Y)
end Action
end AlgebraicGeometry.Scheme.FiniteEtale.Connectedness

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 636171636256b62d49a78872ef0ce439aa3d06d8452e17f706770c915fb8aef8.
Definitions, hypotheses and universes are retained modulo native names. -/
