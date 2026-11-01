/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalPullbackReflection
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite generic universal injectivity on actual Cartesian squares -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Set

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

universe u

private theorem exists_open_constant_genericPoint_membership
    (X : Scheme.{u}) [IrreducibleSpace X] (s : Set X) (hs : IsConstructible s) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧
      ∀ x ∈ U, (x ∈ s ↔ genericPoint X ∈ s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact s hs hsc =>
    by_cases hη : genericPoint X ∈ s
    · exact ⟨⟨s, hs⟩, hη, fun x hx => iff_of_true hx hη⟩
    · refine ⟨⊤, trivial, fun x hx => iff_of_false ?_ hη⟩
      intro hxs
      exact hη ((genericPoint_spec X).mem_open_set_iff hs |>.2 ⟨x, mem_univ x, hxs⟩)
  | union s hs t ht ihs iht =>
    obtain ⟨U, hU, hsU⟩ := ihs
    obtain ⟨V, hV, htV⟩ := iht
    refine ⟨U ⊓ V, ⟨hU, hV⟩, fun x hx => ?_⟩
    exact or_congr (hsU x hx.1) (htV x hx.2)
  | compl s hs ih =>
    obtain ⟨U, hU, hsU⟩ := ih
    exact ⟨U, hU, fun x hx => not_congr (hsU x hx)⟩

/-- A closed subset containing the whole generic fibre of a finite morphism contains
all fibres over some open neighborhood of the generic point. The source closed
subscheme need not be finitely presented. -/
theorem exists_open_generic_fibers_subset_closed_range
    {S W Z : Scheme.{u}} [IrreducibleSpace S] [IsNoetherian S]
    (p : W ⟶ S) [IsFinite p] (i : Z ⟶ W) [IsClosedImmersion i]
    (hη : ∀ w : W, p w = genericPoint S → w ∈ Set.range i) :
    ∃ U : S.Opens, genericPoint S ∈ U ∧
      ∀ w : W, p w ∈ U → w ∈ Set.range i := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian W := { }
  have hbad : IsConstructible (p '' (Set.range i)ᶜ) :=
    p.isConstructible_image ((NoetherianSpace.isCompact _).isConstructible
      i.isClosedEmbedding.isClosed_range.isOpen_compl)
  obtain ⟨U, hU, hconst⟩ := exists_open_constant_genericPoint_membership S _ hbad
  have hnot : genericPoint S ∉ p '' (Set.range i)ᶜ := by
    rintro ⟨w, hw, he⟩
    exact hw (hη w he)
  refine ⟨U, hU, fun w hw => ?_⟩
  by_contra hwi
  exact hnot ((hconst (p w) hw).mp ⟨w, hwi, rfl⟩)

private theorem universallyInjective_pullback_fst_iff_diagonalMap_surjective
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    UniversallyInjective (pullback.fst g f) ↔
      Surjective ((Over.pullback g).map
        (Over.homMk (pullback.diagonal f) :
          Over.mk f ⟶ Over.mk (pullback.snd f f ≫ f))).left := by
  rw [UniversallyInjective.iff_diagonal, diagonal_pullback_fst]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @Surjective),
    MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)]

/-- A relative version of generic radicial spreading. Only the original base is
irreducible; the finite intermediate target may have several components. The
hypothesis says that the actual diagonal covers the fibre over the generic point. -/
theorem exists_open_universallyInjective_of_generic_diagonal
    {X Y S : Scheme.{u}} [IrreducibleSpace S] [IsNoetherian S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f] [IsFinite g]
    (hη : ∀ w : ↥(pullback f f), (pullback.snd f f ≫ f ≫ g) w = genericPoint S →
      w ∈ Set.range (pullback.diagonal f)) :
    ∃ U : S.Opens, genericPoint S ∈ U ∧
      UniversallyInjective (pullback.fst (g ⁻¹ᵁ U).ι f) := by
  let q : pullback f f ⟶ Y := pullback.snd f f ≫ f
  let p : pullback f f ⟶ S := q ≫ g
  let d : Over.mk f ⟶ Over.mk q := Over.homMk (pullback.diagonal f)
  obtain ⟨U, hU, hsubset⟩ :=
    exists_open_generic_fibers_subset_closed_range p (pullback.diagonal f)
      (by simpa only [p, q, Category.assoc] using hη)
  let V : Y.Opens := g ⁻¹ᵁ U
  refine ⟨U, hU,
    (universallyInjective_pullback_fst_iff_diagonalMap_surjective f V.ι).mpr ?_⟩
  constructor
  intro v
  have hvU : p (pullback.fst q V.ι v) ∈ U := by
    have he := congrArg (fun h : pullback q V.ι ⟶ Y => h v)
      (pullback.condition (f := q) (g := V.ι))
    change q (pullback.fst q V.ι v) = V.ι (pullback.snd q V.ι v) at he
    change g (q (pullback.fst q V.ι v)) ∈ U
    rw [he]
    exact (pullback.snd q V.ι v).property
  obtain ⟨a, ha⟩ := hsubset (pullback.fst q V.ι v) hvU
  obtain ⟨z, hz, hza⟩ := exists_preimage_of_isPullback
    (FiniteEtale.PurelyInseparable.Global.overPullback_map_isPullback V.ι d)
    v a ha.symm
  exact ⟨z, hz⟩

/-- Generic universal injectivity spreads over the original irreducible base even
when the finite intermediate target is reducible. -/
theorem exists_open_universallyInjective_of_generic_cartesian_baseChange
    {X Y S T Y' : Scheme.{u}} [IrreducibleSpace S] [IsNoetherian S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f] [IsFinite g]
    (η : T ⟶ S) (t : T) (ht : η t = genericPoint S)
    (k : Y' ⟶ Y) (l : Y' ⟶ T) (hY : IsPullback k l g η)
    [UniversallyInjective (pullback.fst k f)] :
    ∃ U : S.Opens, genericPoint S ∈ U ∧
      UniversallyInjective (pullback.fst (g ⁻¹ᵁ U).ι f) := by
  apply exists_open_universallyInjective_of_generic_diagonal f g
  let q : pullback f f ⟶ Y := pullback.snd f f ≫ f
  let d : Over.mk f ⟶ Over.mk q := Over.homMk (pullback.diagonal f)
  have hk : Surjective ((Over.pullback k).map d).left :=
    (universallyInjective_pullback_fst_iff_diagonalMap_surjective f k).mp inferInstance
  intro w hw
  change g (q w) = genericPoint S at hw
  obtain ⟨c, hc, hct⟩ := exists_preimage_of_isPullback hY (q w) t
    (show g (q w) = η t from hw.trans ht.symm)
  obtain ⟨v, hv, hvc⟩ := Pullback.exists_preimage_pullback (f := q) (g := k) w c hc.symm
  obtain ⟨a, ha⟩ := hk.surj v
  refine ⟨pullback.fst f k a, ?_⟩
  have he := congrArg (fun h : pullback f k ⟶ pullback f f => h a)
    (show ((Over.pullback k).map d).left ≫ pullback.fst q k =
      pullback.fst f k ≫ pullback.diagonal f from pullback.lift_fst _ _ _)
  change pullback.fst q k (((Over.pullback k).map d).left a) =
    pullback.diagonal f (pullback.fst f k a) at he
  exact he.symm.trans ((congrArg (fun z => pullback.fst q k z) ha).trans hv)

end AlgebraicGeometry.Scheme
