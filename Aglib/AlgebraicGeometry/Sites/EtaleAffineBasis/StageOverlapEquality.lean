/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.BaseChangeRepresentativeSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteBaseChangeEqualities
/-! # Actual finite-stage overlap matching from a limit section -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Matching on the actual base changes of all pairwise overlaps. -/
def BaseChangeOverlapMatching {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j))) : Prop :=
  ∀ j k, etaleRepresentativeSection F
      (relativeBaseChangeObject τ r (pullback.fst (W j).hom (W k).hom ≫ (W j).hom))
      (U j) (relativeBaseChangeOverlapLeft τ r (W j).hom (W k).hom ≫
        relativeBaseChangeRepresentative τ r (W j).hom (U j) (a j) (ha j)) (t j) =
    etaleRepresentativeSection F
      (relativeBaseChangeObject τ r (pullback.fst (W j).hom (W k).hom ≫ (W j).hom))
      (U k) (relativeBaseChangeOverlapRight τ r (W j).hom (W k).hom ≫
        relativeBaseChangeRepresentative τ r (W k).hom (U k) (a k) (ha k)) (t k)

/-- A single original section at the limit produces genuine overlap matching
at one common finite stage. No matching or continuity at that stage is assumed. -/
theorem exists_stage_overlap_matching
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} [Finite J]
    (W : J → Over (D.obj i)) [∀ j, IsAffine (W j).left]
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (c.π.app i ≫ r))))
    (hs : ∀ j, (pullbackSectionsFunctor F).map
        (relativeBaseChangeSource (c.π.app i) r (W j).hom).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject (c.π.app i) r (W j).hom)
        (U j) (relativeBaseChangeRepresentative (c.π.app i) r (W j).hom
          (U j) (a j) (ha j)) (t j)) :
    ∃ k : Over i, BaseChangeOverlapMatching (D.map k.hom) r F W U a ha t := by
  let Z (p : J × J) : Over (D.obj i) :=
    Over.mk (pullback.fst (W p.1).hom (W p.2).hom ≫ (W p.1).hom)
  let A (p : J × J) := pullback.fst (W p.1).hom (W p.2).hom ≫ a p.1
  let B (p : J × J) := pullback.snd (W p.1).hom (W p.2).hom ≫ a p.2
  have hA (p : J × J) : A p ≫ (U p.1).hom = (Z p).hom ≫ r :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ pullback.fst (W p.1).hom (W p.2).hom ≫ z) (ha p.1)).trans
        (Category.assoc _ _ _).symm)
  have hB (p : J × J) : B p ≫ (U p.2).hom = (Z p).hom ≫ r :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ pullback.snd (W p.1).hom (W p.2).hom ≫ z) (ha p.2)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ r) pullback.condition.symm)))
  have (p : J × J) : IsAffine (Z p).left :=
    inferInstanceAs (IsAffine (pullback (W p.1).hom (W p.2).hom))
  have hL {T : Scheme.{u}} (τ : T ⟶ D.obj i) (p : J × J) :
      relativeBaseChangeOverlapLeft τ r (W p.1).hom (W p.2).hom ≫
          relativeBaseChangeRepresentative τ r (W p.1).hom (U p.1) (a p.1) (ha p.1) =
        relativeBaseChangeRepresentative τ r (Z p).hom (U p.1) (A p) (hA p) := by
    apply Over.OverMorphism.ext
    change overlapBaseChangeLeft τ (W p.1).hom (W p.2).hom ≫
      (pullback.snd τ (W p.1).hom ≫ a p.1) = pullback.snd τ
        (pullback.fst (W p.1).hom (W p.2).hom ≫ (W p.1).hom) ≫
          (pullback.fst (W p.1).hom (W p.2).hom ≫ a p.1)
    simp only [overlapBaseChangeLeft, pullback.lift_snd_assoc, Category.assoc]
  have hR {T : Scheme.{u}} (τ : T ⟶ D.obj i) (p : J × J) :
      relativeBaseChangeOverlapRight τ r (W p.1).hom (W p.2).hom ≫
          relativeBaseChangeRepresentative τ r (W p.2).hom (U p.2) (a p.2) (ha p.2) =
        relativeBaseChangeRepresentative τ r (Z p).hom (U p.2) (B p) (hB p) := by
    apply Over.OverMorphism.ext
    change overlapBaseChangeRight τ (W p.1).hom (W p.2).hom ≫
      (pullback.snd τ (W p.2).hom ≫ a p.2) = pullback.snd τ
        (pullback.fst (W p.1).hom (W p.2).hom ≫ (W p.1).hom) ≫
          (pullback.snd (W p.1).hom (W p.2).hom ≫ a p.2)
    simp only [overlapBaseChangeRight, pullback.lift_snd_assoc, Category.assoc]
  have hlimit (p : J × J) := relativeBaseChange_representatives_overlap (c.π.app i) r
    (W p.1).hom (W p.2).hom F (U p.1) (U p.2) (a p.1) (a p.2)
      (ha p.1) (ha p.2) (t p.1) (t p.2) s (hs p.1) (hs p.2)
  have hraw (p : J × J) :=
    (congrArg (fun q ↦ etaleRepresentativeSection F
      (relativeBaseChangeObject (c.π.app i) r (Z p).hom) (U p.1) q (t p.1))
      (hL (c.π.app i) p)).symm.trans
      ((hlimit p).trans (congrArg (fun q ↦ etaleRepresentativeSection F
        (relativeBaseChangeObject (c.π.app i) r (Z p).hom) (U p.2) q (t p.2))
        (hR (c.π.app i) p)))
  obtain ⟨k, hk⟩ := exists_common_baseChange_representatives_eventually_equal D c hc i r F Z
    (fun p ↦ U p.1) (fun p ↦ U p.2) A B hA hB
    (fun p ↦ t p.1) (fun p ↦ t p.2) hraw
  refine ⟨k, fun j l ↦ ?_⟩
  exact (congrArg (fun q ↦ etaleRepresentativeSection F
      (relativeBaseChangeObject (D.map k.hom) r (Z (j, l)).hom) (U j) q (t j))
      (hL (D.map k.hom) (j, l))).trans
    ((hk (j, l)).trans (congrArg (fun q ↦ etaleRepresentativeSection F
      (relativeBaseChangeObject (D.map k.hom) r (Z (j, l)).hom) (U l) q (t l))
      (hR (D.map k.hom) (j, l))).symm)
end AlgebraicGeometry.Scheme.EtaleAffineBasis
