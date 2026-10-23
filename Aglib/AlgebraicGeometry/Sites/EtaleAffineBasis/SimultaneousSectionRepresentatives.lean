/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteSectionRepresentatives
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRefinement

/-! # Simultaneous finite affine representatives of two original sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v w

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Two original covering families admit a common finite affine refinement over
any quasi-compact site object. Affineness of scheme fiber products is not used. -/
theorem exists_finite_affine_common_refinement {S : Scheme.{u}} (T : S.Etale)
    [CompactSpace T.left] {J : Type v} {K : Type w}
    (W : J → S.Etale) (V : K → S.Etale)
    (f : ∀ j, W j ⟶ T) (g : ∀ k, V k ⟶ T)
    (hf : Sieve.ofArrows W f ∈ S.smallEtaleTopology T)
    (hg : Sieve.ofArrows V g ∈ S.smallEtaleTopology T) :
    ∃ (L : Type u) (_ : Finite L) (R : L → S.Etale) (r : ∀ l, R l ⟶ T),
      (∀ l, IsAffine (R l).left) ∧
      (Sieve.ofArrows R r ∈ S.smallEtaleTopology T) ∧
      ∀ l, ∃ (j : J) (k : K) (a : R l ⟶ W j) (b : R l ⟶ V k),
        a ≫ f j = r l ∧ b ≫ g k = r l := by
  obtain ⟨L, hL, R, r, hR, hr, hcov⟩ := exists_finite_affine_family T
    (Sieve.ofArrows W f ⊓ Sieve.ofArrows V g)
    (S.smallEtaleTopology.intersection_covering hf hg)
  refine ⟨L, hL, R, r, hR, hcov, fun l ↦ ?_⟩
  obtain ⟨j, a, ha⟩ := (Sieve.mem_ofArrows_iff W f (r l)).mp (hr l).1
  obtain ⟨k, b, hb⟩ := (Sieve.mem_ofArrows_iff V g (r l)).mp (hr l).2
  exact ⟨j, k, a, b, ha.symm, hb.symm⟩

/-- Restrict an equality to an original representative along an arbitrary
relative arrow, preserving the native representative interface. -/
theorem representative_restriction_of_eq {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z B : Over X}
    (a : Y ⟶ B) (b : Z ⟶ Y) (U : X.Etale)
    (c : Y ⟶ (Etale.forget X).obj U)
    (s : (globalSections B.left).obj ((inverseImage B.hom).obj F))
    (t : F.obj.obj (op U))
    (h : pullbackSectionsMap F a s = etaleRepresentativeSection F Y U c t) :
    pullbackSectionsMap F (b ≫ a) s =
      etaleRepresentativeSection F Z U (b ≫ c) t := by
  have hr : pullbackSectionsMap F b (etaleRepresentativeSection F Y U c t) =
      etaleRepresentativeSection F Z U (b ≫ c) t :=
    etaleRepresentativeSection_restrict F b U c t
  exact (ConcreteCategory.congr_hom (pullbackSectionsMap_comp F b a) s).trans
    ((ConcreteCategory.comp_apply _ _ _).trans
      ((congrArg (pullbackSectionsMap F b) h).trans hr))

/-- Refining a chart retains the original coefficient representative and the
literal original section restriction equation. -/
theorem section_representative_refinement {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {W V : S.Etale} (b : V ⟶ W)
    (U : X.Etale) (a : Over.mk (W.hom ≫ f) ⟶ (Etale.forget X).obj U)
    (s : (globalSections S).obj ((inverseImage f).obj F))
    (t : F.obj.obj (op U))
    (h : pullbackSectionsMap F
      (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) s =
        etaleRepresentativeSection F (Over.mk (W.hom ≫ f)) U a t) :
    ∃ (c : Over.mk (V.hom ≫ f) ⟶ (Etale.forget X).obj U),
      pullbackSectionsMap F
        (Over.homMk V.hom (U := Over.mk (V.hom ≫ f)) (V := Over.mk f)) s =
          etaleRepresentativeSection F (Over.mk (V.hom ≫ f)) U c t := by
  let d : Over.mk (V.hom ≫ f) ⟶ Over.mk (W.hom ≫ f) :=
    Over.homMk b.left (by
      exact (Category.assoc b.left W.hom f).symm.trans
        (congrArg (fun q ↦ q ≫ f) (MorphismProperty.Over.w b)))
  let q : Over.mk (W.hom ≫ f) ⟶ Over.mk f := Over.homMk W.hom
  have hd : d ≫ q =
      Over.homMk V.hom (U := Over.mk (V.hom ≫ f)) (V := Over.mk f) := by
    apply Over.OverMorphism.ext
    exact MorphismProperty.Over.w b
  refine ⟨d ≫ a, ?_⟩
  have he := representative_restriction_of_eq F
    (Y := Over.mk (W.hom ≫ f)) (Z := Over.mk (V.hom ≫ f))
    (B := Over.mk f) q d U a s t h
  have hd' : pullbackSectionsMap F (d ≫ q) s =
      pullbackSectionsMap F
        (Over.homMk V.hom (U := Over.mk (V.hom ≫ f)) (V := Over.mk f)) s :=
    congrArg (fun k : Over.mk (V.hom ≫ f) ⟶ Over.mk f ↦
      pullbackSectionsMap F k s) hd
  exact hd'.symm.trans he

/-- Two original relative global sections admit simultaneous representatives
on one actual finite affine covering family. No continuity hypothesis or
assumption about affine products over a non-affine base occurs. -/
theorem exists_finite_affine_simultaneous_section_representatives
    {X S : Scheme.{u}} [CompactSpace S] (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X)
    (s t : (globalSections S).obj ((inverseImage f).obj F)) :
    ∃ (J : Type u) (_ : Finite J) (W : J → S.Etale),
      (∀ j, IsAffine (W j).left) ∧
      (Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) ∈
        S.smallEtaleTopology (etaleTerminal S)) ∧
      ∀ j, ∃ (U V : X.Etale)
        (a : Over.mk ((W j).hom ≫ f) ⟶ (Etale.forget X).obj U)
        (b : Over.mk ((W j).hom ≫ f) ⟶ (Etale.forget X).obj V)
        (x : F.obj.obj (op U)) (y : F.obj.obj (op V)),
        (pullbackSectionsMap F
          (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)) s =
            etaleRepresentativeSection F (Over.mk ((W j).hom ≫ f)) U a x) ∧
        (pullbackSectionsMap F
          (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)) t =
            etaleRepresentativeSection F (Over.mk ((W j).hom ≫ f)) V b y) := by
  obtain ⟨J, _, W, _, hW, hs⟩ := exists_finite_affine_section_representatives f F s
  obtain ⟨K, _, V, _, hV, ht⟩ := exists_finite_affine_section_representatives f F t
  have : CompactSpace (etaleTerminal S).left := inferInstanceAs (CompactSpace S)
  obtain ⟨L, hL, R, r, hR, hcov, href⟩ :=
    exists_finite_affine_common_refinement (etaleTerminal S) W V
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j))
      (fun k ↦ (etaleTerminalIsTerminal S).from (V k)) hW hV
  have hr : r = fun l ↦ (etaleTerminalIsTerminal S).from (R l) :=
    funext fun l ↦ (etaleTerminalIsTerminal S).hom_ext _ _
  refine ⟨L, hL, R, hR, hr ▸ hcov, fun l ↦ ?_⟩
  obtain ⟨j, k, a, b, _, _⟩ := href l
  obtain ⟨U, c, x, hx⟩ := hs j
  obtain ⟨V, d, y, hy⟩ := ht k
  obtain ⟨c', hc⟩ := section_representative_refinement f F a U c s x hx
  obtain ⟨d', hd⟩ := section_representative_refinement f F b V d t y hy
  exact ⟨U, V, c', d', x, y, hc, hd⟩

end AlgebraicGeometry.Scheme.EtaleAffineBasis
