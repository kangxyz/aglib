/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.BaseChangeUnitMatching
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.UnitSectionsAmalgamation
/-! # A genuine stage section obtained from finite limit representatives -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The actual base-changed family is a cover in the original small etale site. -/
theorem baseChangeEtaleChart_covering {S T : Scheme.{u}} (τ : T ⟶ S)
    {J : Type v} (W : J → Over S) [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x) :
    Sieve.ofArrows (fun j ↦ baseChangeEtaleChart τ (W j))
      (fun j ↦ (etaleTerminalIsTerminal T).from (baseChangeEtaleChart τ (W j))) ∈
      T.smallEtaleTopology (etaleTerminal T) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, y, hy⟩ := hcover (τ x)
  have hx : x ∈ Set.range (pullback.fst τ (W j).hom) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  apply Set.mem_iUnion.mpr
  refine ⟨j, z, ?_⟩
  have hw := MorphismProperty.Over.w
    ((etaleTerminalIsTerminal T).from (baseChangeEtaleChart τ (W j)))
  have hleft : ((etaleTerminalIsTerminal T).from
      (baseChangeEtaleChart τ (W j))).left = pullback.fst τ (W j).hom :=
    (Category.comp_id _).symm.trans hw
  exact (congrArg (fun q ↦ q z) hleft).trans hz

/-- Finite affine local representatives of one actual limit section give a
section in the original inverse-image sheaf at a common stage. Its local
restriction equations are literal original relative section equations. -/
theorem exists_stage_section_amalgamating_representatives
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} [Finite J]
    (W : J → Over (D.obj i)) [∀ j, IsAffine (W j).left] [∀ j, Etale (W j).hom]
    (hcover : ∀ x : D.obj i, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (c.π.app i ≫ r))))
    (hs : ∀ j, (pullbackSectionsFunctor F).map
        (relativeBaseChangeSource (c.π.app i) r (W j).hom).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject (c.π.app i) r (W j).hom)
        (U j) (relativeBaseChangeRepresentative (c.π.app i) r (W j).hom
          (U j) (a j) (ha j)) (t j)) :
    ∃ (k : Over i)
      (v : (globalSections (D.obj k.left)).obj ((inverseImage (D.map k.hom ≫ r)).obj F)),
      ∀ j, pullbackSectionsMap F
        (Over.homMk (baseChangeEtaleChart (D.map k.hom) (W j)).hom
          (U := Over.mk ((baseChangeEtaleChart (D.map k.hom) (W j)).hom ≫
            (D.map k.hom ≫ r))) (V := Over.mk (D.map k.hom ≫ r))) v =
        etaleRepresentativeSection F
          (Over.mk ((baseChangeEtaleChart (D.map k.hom) (W j)).hom ≫ (D.map k.hom ≫ r)))
          (U j) (unitRepresentativeArrow (D.map k.hom ≫ r)
            (baseChangeChartTest (D.map k.hom) r (W j) (U j) (a j) (ha j))) (t j) := by
  obtain ⟨k, hk⟩ := exists_stage_overlap_matching D c hc i r F W U a ha t s hs
  have hcomp := baseChange_unitSections_compatible (D.map k.hom) r F W U a ha t hk
  obtain ⟨v, hv⟩ := exists_unitSections_amalgamation (D.map k.hom ≫ r) F
    (fun j ↦ baseChangeEtaleChart (D.map k.hom) (W j)) U
    (fun j ↦ baseChangeChartTest (D.map k.hom) r (W j) (U j) (a j) (ha j)) t
    (baseChangeEtaleChart_covering (D.map k.hom) W hcover) hcomp
  exact ⟨k, v, hv⟩
end AlgebraicGeometry.Scheme.EtaleAffineBasis
