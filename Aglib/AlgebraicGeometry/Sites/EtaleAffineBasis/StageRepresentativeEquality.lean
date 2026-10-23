/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.WitnessCoverDescent
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections

/-! # Eventual equality of original sections from finite local witnesses -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Original coefficient sections with modeled finite covering witnesses agree
at an actual common stage. Both section values use the original relative
section functor and the original chart evaluation isomorphisms. -/
theorem exists_stage_etaleRepresentativeSection_eq
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} [Finite J] (Z : J → Over (D.obj i))
    [∀ j, QuasiCompact (Z j).hom] [∀ j, QuasiSeparated (Z j).hom]
    [∀ j, Etale (Z j).hom]
    (hcover : ∀ x : D.obj i, ∃ j, ∃ y : (Z j).left, (Z j).hom y = x)
    (U V : X.Etale) (a : D.obj i ⟶ U.left) (b : D.obj i ⟶ V.left)
    (ha : a ≫ U.hom = r) (hb : b ≫ V.hom = r)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (T : J → X.Etale) (p : ∀ j, T j ⟶ U) (q : ∀ j, T j ⟶ V)
    (w : ∀ j, pullback (c.π.app i) (Z j).hom ⟶ (T j).left)
    (hw : ∀ j, w j ≫ (T j).hom =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ r)
    (hp : ∀ j, w j ≫ (p j).left =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ a)
    (hq : ∀ j, w j ≫ (q j).left =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ b)
    (hst : ∀ j, F.obj.map (p j).op s = F.obj.map (q j).op t) :
    ∃ k : Over i,
      etaleRepresentativeSection F (Over.mk (D.map k.hom ≫ r)) U
          (Over.homMk (D.map k.hom ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ D.map k.hom ≫ z) ha))) s =
        etaleRepresentativeSection F (Over.mk (D.map k.hom ≫ r)) V
          (Over.homMk (D.map k.hom ≫ b) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ D.map k.hom ≫ z) hb))) t := by
  obtain ⟨k, d, hdp, hdq, _, hcov⟩ := exists_covering_witness_models D c hc i r Z hcover
    T (fun _ ↦ U) (fun _ ↦ V) (fun _ ↦ a) (fun _ ↦ b)
    (fun _ ↦ ha) (fun _ ↦ hb) p q w hw hp hq
  let f := D.map k.hom ≫ r
  let W (j : J) : (D.obj k.left).Etale :=
    Scheme.Etale.mk (pullback.fst (D.map k.hom) (Z j).hom)
  let A : Over.mk f ⟶ (Etale.forget X).obj U :=
    Over.homMk (D.map k.hom ≫ a) ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ D.map k.hom ≫ z) ha))
  let B : Over.mk f ⟶ (Etale.forget X).obj V :=
    Over.homMk (D.map k.hom ≫ b) ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ D.map k.hom ≫ z) hb))
  have hwp (j : J) : d j ≫ (p j).left = (W j).hom ≫ A.left := by
    exact (hdp j).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ a) (pullback.condition
        (f := D.map k.hom) (g := (Z j).hom)).symm).trans (Category.assoc _ _ _)))
  have hwq (j : J) : d j ≫ (q j).left = (W j).hom ≫ B.left := by
    exact (hdq j).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ b) (pullback.condition
        (f := D.map k.hom) (g := (Z j).hom)).symm).trans (Category.assoc _ _ _)))
  let C (j : J) : Over.mk ((W j).hom ≫ f) ⟶ (Etale.forget X).obj (T j) :=
    Over.homMk (d j) (by
      have hpstruct := MorphismProperty.Over.w (p j)
      exact (congrArg (fun z ↦ d j ≫ z) hpstruct.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ U.hom) (hwp j)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun z ↦ (W j).hom ≫ z) (Over.w A))))))
  have hW : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal _).from (W j)) ∈
      (D.obj k.left).smallEtaleTopology (etaleTerminal (D.obj k.left)) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, y, hy⟩ := hcov x
    apply Set.mem_iUnion.mpr
    refine ⟨j, y, ?_⟩
    have hterminal := MorphismProperty.Over.w ((etaleTerminalIsTerminal _).from (W j))
    have hleft : ((etaleTerminalIsTerminal _).from (W j)).left = (W j).hom :=
      (Category.comp_id _).symm.trans hterminal
    exact (congrArg (fun z ↦ z y) hleft).trans hy
  refine ⟨k, ?_⟩
  apply etaleRepresentativeSection_eq_of_covering_witnesses f F W hW U V A B s t T p q C
  · intro j
    apply Over.OverMorphism.ext
    exact hwp j
  · intro j
    apply Over.OverMorphism.ext
    exact hwq j
  · exact hst

end AlgebraicGeometry.Scheme.EtaleAffineBasis
