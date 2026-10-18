/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! Reflection of isomorphisms and its actual clopen local locus.
The bad covers are the nonimage and the off-diagonal of a finite-etale
morphism. No Galois-category or fibre-functor axiom is used. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.Connectedness

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite forget
  pointToPreimage_surjective)

universe u
variable {X : Scheme.{u}}

attribute [local instance] hom_isFinite hom_etale

theorem structural_range_isClopen (Y : Scheme.FiniteEtale X) :
    IsClopen (Set.range Y.obj.hom) :=
  ⟨Y.obj.hom.isClosedMap.isClosed_range, Y.obj.hom.isOpenMap.isOpen_range⟩

theorem nonempty_fiber_of_nonempty_cover [ConnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) [Nonempty Y.obj.left] :
    Nonempty (Fiber s Y) := by
  have hr : Set.range Y.obj.hom = Set.univ :=
    (structural_range_isClopen Y).eq_univ (Set.range_nonempty _)
  obtain ⟨y, hy⟩ := Set.range_eq_univ.mp hr (s default)
  obtain ⟨p, _⟩ := pointToPreimage_surjective s Y ⟨y, hy⟩
  exact ⟨p⟩

theorem isEmpty_cover_of_isEmpty_fiber [ConnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) [IsEmpty (Fiber s Y)] :
    IsEmpty Y.obj.left := by
  constructor
  intro y
  let : Nonempty Y.obj.left := ⟨y⟩
  obtain ⟨p⟩ := nonempty_fiber_of_nonempty_cover s Y
  exact isEmptyElim p

/-- The diagonal morphism of `f`, regarded as a morphism of finite étale covers. -/
def coverDiagonal {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Y ⟶ pullbackCover f f :=
  ObjectProperty.homMk (Over.homMk (pullback.diagonal f.hom.left) (by
    change pullback.diagonal f.hom.left ≫ pullback.fst f.hom.left f.hom.left ≫
      Y.obj.hom = Y.obj.hom
    simp))

/-- The open complement in `Z` of the image of `f`. -/
def nonimageOpen {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Z.obj.left.Opens :=
  ⟨(Set.range f.hom.left)ᶜ, (hom_range_isClopen f).1.isOpen_compl⟩

/-- The finite étale cover obtained by restricting `Z` to the complement of the image of `f`. -/
def nonimageCover {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Scheme.FiniteEtale X :=
  clopenCover Z (nonimageOpen f) (hom_range_isClopen f).2.isClosed_compl

/-- The open complement of the diagonal image in the self-pullback of `f`. -/
def offDiagonalOpen {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) :
    (pullbackCover f f).obj.left.Opens :=
  ⟨(Set.range (coverDiagonal f).hom.left)ᶜ,
    (hom_range_isClopen (coverDiagonal f)).1.isOpen_compl⟩

/-- The finite étale cover on the complement of the diagonal image in the self-pullback of `f`. -/
def offDiagonalCover {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : Scheme.FiniteEtale X :=
  clopenCover (pullbackCover f f) (offDiagonalOpen f)
    (hom_range_isClopen (coverDiagonal f)).2.isClosed_compl

theorem isEmpty_nonimageFiber_of_surjective {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z)
    (h : Function.Surjective ((fiberToFinite s).map f)) :
    IsEmpty (Fiber s (nonimageCover f)) := by
  constructor
  intro p
  let j : nonimageCover f ⟶ Z :=
    clopenCoverι Z (nonimageOpen f) (hom_range_isClopen f).2.isClosed_compl
  let q : Fiber s Z := p ≫ j.hom
  obtain ⟨r, hr⟩ := h q
  have hp : (nonimageOpen f).ι (p.left (default : Spec (CommRingCat.of K))) ∉
      Set.range f.hom.left := (p.left (default : Spec (CommRingCat.of K))).property
  apply hp
  refine ⟨r.left (default : Spec (CommRingCat.of K)), ?_⟩
  exact congrArg (fun a : Fiber s Z => a.left (default : Spec (CommRingCat.of K))) hr

theorem isEmpty_offDiagonalFiber_of_injective {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z)
    (h : Function.Injective ((fiberToFinite s).map f)) :
    IsEmpty (Fiber s (offDiagonalCover f)) := by
  constructor
  intro p
  let j : offDiagonalCover f ⟶ pullbackCover f f :=
    clopenCoverι (pullbackCover f f) (offDiagonalOpen f)
      (hom_range_isClopen (coverDiagonal f)).2.isClosed_compl
  let q : Fiber s (pullbackCover f f) := p ≫ j.hom
  let a : Fiber s Y := q ≫ (pullbackCoverFst f f).hom
  let b : Fiber s Y := q ≫ (pullbackCoverSnd f f).hom
  have hab : a = b := h (by
    apply Over.OverMorphism.ext
    change (q.left ≫ pullback.fst f.hom.left f.hom.left) ≫ f.hom.left =
      (q.left ≫ pullback.snd f.hom.left f.hom.left) ≫ f.hom.left
    rw [Category.assoc, Category.assoc, pullback.condition])
  have hq : q.left = a.left ≫ pullback.diagonal f.hom.left := by
    apply pullback.hom_ext
    · change q.left ≫ pullback.fst f.hom.left f.hom.left =
        (q.left ≫ pullback.fst f.hom.left f.hom.left) ≫
          pullback.diagonal f.hom.left ≫ pullback.fst f.hom.left f.hom.left
      simp
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (congrArg (fun t : Fiber s Y => t.left) hab).symm
  have hp : (offDiagonalOpen f).ι (p.left (default : Spec (CommRingCat.of K))) ∉
      Set.range (coverDiagonal f).hom.left :=
    (p.left (default : Spec (CommRingCat.of K))).property
  apply hp
  refine ⟨a.left (default : Spec (CommRingCat.of K)), ?_⟩
  exact (congrArg (fun t : Spec (CommRingCat.of K) ⟶ (pullbackCover f f).obj.left =>
    t default) hq).symm

theorem isIso_of_empty_bad_covers {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z)
    [IsEmpty (nonimageCover f).obj.left] [IsEmpty (offDiagonalCover f).obj.left] :
    IsIso f := by
  have hsurj : Surjective f.hom.left := ⟨fun z => by
    by_contra hz
    exact isEmptyElim (show (nonimageCover f).obj.left from ⟨z, hz⟩)⟩
  let := hsurj
  have hd : Surjective (pullback.diagonal f.hom.left) := ⟨fun p => by
    by_contra hp
    exact isEmptyElim (show (offDiagonalCover f).obj.left from ⟨p, hp⟩)⟩
  let := hd
  have : IsIso (pullback.diagonal f.hom.left) :=
    Flat.isIso_of_surjective_of_mono _
  have hp : pullback.fst f.hom.left f.hom.left =
      pullback.snd f.hom.left f.hom.left := by
    apply (cancel_epi (pullback.diagonal f.hom.left)).mp
    simp
  have : Mono f.hom.left := by
    constructor
    intro T a b hab
    have he := congrArg (fun p => pullback.lift a b hab ≫ p) hp
    simpa only [pullback.lift_fst, pullback.lift_snd] using he
  have : IsIso f.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget X).map f.hom) := by
    change IsIso f.hom.left
    infer_instance
  have : IsIso ((forget X).map f) := by
    change IsIso f.hom
    exact isIso_of_reflects_iso f.hom (Over.forget X)
  exact isIso_of_reflects_iso f (forget X)

theorem isIso_of_bijective_fiber [ConnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z)
    (h : Function.Bijective ((fiberToFinite s).map f)) : IsIso f := by
  let : IsEmpty (Fiber s (nonimageCover f)) :=
    isEmpty_nonimageFiber_of_surjective s f h.2
  let : IsEmpty (Fiber s (offDiagonalCover f)) :=
    isEmpty_offDiagonalFiber_of_injective s f h.1
  let : IsEmpty (nonimageCover f).obj.left :=
    isEmpty_cover_of_isEmpty_fiber s _
  let : IsEmpty (offDiagonalCover f).obj.left :=
    isEmpty_cover_of_isEmpty_fiber s _
  exact isIso_of_empty_bad_covers f

theorem point_not_mem_structural_range_of_isEmpty_fiber
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) [IsEmpty (Fiber s Y)] :
    s default ∉ Set.range Y.obj.hom := by
  rintro ⟨y, hy⟩
  obtain ⟨p, _⟩ := pointToPreimage_surjective s Y ⟨y, hy⟩
  exact isEmptyElim p

/-- The open complement in `X` of the structural images of the nonimage and off-diagonal covers. -/
def isomorphismOpen {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) : X.Opens :=
  ⟨(Set.range (nonimageCover f).obj.hom ∪ Set.range (offDiagonalCover f).obj.hom)ᶜ,
    ((structural_range_isClopen (nonimageCover f)).1.union
      (structural_range_isClopen (offDiagonalCover f)).1).isOpen_compl⟩

theorem isClopen_isomorphismOpen {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) :
    IsClopen (isomorphismOpen f : Set X) :=
  ⟨((structural_range_isClopen (nonimageCover f)).2.union
      (structural_range_isClopen (offDiagonalCover f)).2).isClosed_compl,
    (isomorphismOpen f).isOpen⟩

theorem mem_isomorphismOpen_of_bijective_fiber
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z)
    (h : Function.Bijective ((fiberToFinite s).map f)) :
    s default ∈ isomorphismOpen f := by
  let : IsEmpty (Fiber s (nonimageCover f)) :=
    isEmpty_nonimageFiber_of_surjective s f h.2
  let : IsEmpty (Fiber s (offDiagonalCover f)) :=
    isEmpty_offDiagonalFiber_of_injective s f h.1
  exact fun hx => hx.elim
    (point_not_mem_structural_range_of_isEmpty_fiber s _)
    (point_not_mem_structural_range_of_isEmpty_fiber s _)

theorem isIso_baseChange_isomorphismOpen {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) :
    IsIso ((baseChange (isomorphismOpen f).ι).map f) := by
  classical
  let U := isomorphismOpen f
  let Y' := (baseChange U.ι).obj Y
  let Z' := (baseChange U.ι).obj Z
  let f' : Y' ⟶ Z' := (baseChange U.ι).map f
  let iY : Y'.obj.left ⟶ Y.obj.left := pullback.fst Y.obj.hom U.ι
  let iZ : Z'.obj.left ⟶ Z.obj.left := pullback.fst Z.obj.hom U.ι
  have hY : iY ≫ Y.obj.hom = Y'.obj.hom ≫ U.ι := pullback.condition
  have hZ : iZ ≫ Z.obj.hom = Z'.obj.hom ≫ U.ι := pullback.condition
  have hf : f'.hom.left ≫ iZ = iY ≫ f.hom.left := by
    change pullback.lift (iY ≫ f.hom.left) Y'.obj.hom _ ≫
      pullback.fst Z.obj.hom U.ι = iY ≫ f.hom.left
    exact pullback.lift_fst _ _ _
  have : Mono iY := by
    change Mono (pullback.fst Y.obj.hom U.ι)
    infer_instance
  have : IsOpenImmersion iZ := by
    change IsOpenImmersion (pullback.fst Z.obj.hom U.ι)
    infer_instance
  have : Mono f'.hom.left := by
    constructor
    intro T a b hab
    have hab' : (a ≫ iY) ≫ f.hom.left = (b ≫ iY) ≫ f.hom.left := by
      rw [Category.assoc, Category.assoc, ← hf, ← Category.assoc, ← Category.assoc, hab]
    let q : T ⟶ (pullbackCover f f).obj.left :=
      pullback.lift (a ≫ iY) (b ≫ iY) hab'
    have hq : Set.range q ⊆ Set.range (pullback.diagonal f.hom.left) := by
      rintro _ ⟨t, rfl⟩
      by_contra hp
      let p : (offDiagonalCover f).obj.left := ⟨q t, hp⟩
      have he : (offDiagonalCover f).obj.hom p = U.ι (Y'.obj.hom (a t)) := by
        change ((q ≫ pullback.fst f.hom.left f.hom.left) ≫ Y.obj.hom) t =
          ((a ≫ Y'.obj.hom) ≫ U.ι) t
        dsimp only [q]
        rw [pullback.lift_fst, Category.assoc, hY, Category.assoc]
      have ht : U.ι (Y'.obj.hom (a t)) ∈ U := (Y'.obj.hom (a t)).property
      exact ht (Or.inr ⟨p, he⟩)
    let l := IsOpenImmersion.lift (pullback.diagonal f.hom.left) q hq
    have hl : l ≫ pullback.diagonal f.hom.left = q := IsOpenImmersion.lift_fac _ _ _
    apply (cancel_mono iY).mp
    calc
      a ≫ iY = q ≫ pullback.fst f.hom.left f.hom.left :=
        (pullback.lift_fst _ _ _).symm
      _ = l := by rw [← hl]; simp
      _ = q ≫ pullback.snd f.hom.left f.hom.left := by rw [← hl]; simp
      _ = b ≫ iY := pullback.lift_snd _ _ _
  have : Surjective f'.hom.left := ⟨fun z => by
    let x := Z'.obj.hom z
    have hx : U.ι x ∈ U := x.property
    have hz : iZ z ∈ Set.range f.hom.left := by
      by_contra hp
      let p : (nonimageCover f).obj.left := ⟨iZ z, hp⟩
      have he : (nonimageCover f).obj.hom p = U.ι x := by
        change (iZ ≫ Z.obj.hom) z = (Z'.obj.hom ≫ U.ι) z
        rw [hZ]
      exact hx (Or.inl ⟨p, he⟩)
    obtain ⟨y, hy⟩ := hz
    have hyx : Y.obj.hom y = U.ι x := by
      rw [← Over.w f.hom]
      change Z.obj.hom (f.hom.left y) = U.ι x
      rw [hy]
      exact congrArg (fun k : Z'.obj.left ⟶ X => k z) hZ
    obtain ⟨p, hp, hpx⟩ := Scheme.Pullback.exists_preimage_pullback y x hyx
    refine ⟨p, iZ.injective ?_⟩
    change (f'.hom.left ≫ iZ) p = iZ z
    rw [hf]
    change f.hom.left ((pullback.fst Y.obj.hom U.ι) p) = iZ z
    rw [hp, hy]⟩
  have : IsIso f'.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget U.toScheme).map f'.hom) := by
    change IsIso f'.hom.left
    infer_instance
  have : IsIso ((forget U.toScheme).map f') := by
    change IsIso f'.hom
    exact isIso_of_reflects_iso f'.hom (Over.forget U.toScheme)
  exact isIso_of_reflects_iso f' (forget U.toScheme)

theorem exists_open_isIso_of_bijective_fiber
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z)
    (h : Function.Bijective ((fiberToFinite s).map f)) :
    ∃ U : X.Opens, s default ∈ U ∧ IsIso ((baseChange U.ι).map f) :=
  ⟨isomorphismOpen f, mem_isomorphismOpen_of_bijective_fiber s f h,
    isIso_baseChange_isomorphismOpen f⟩

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d4dcda7c3ba8b51fe261d6db271fbb810bb442ceca9e71c25765a0acfaa7760e.
Definitions, hypotheses and universes are retained modulo native names. -/
