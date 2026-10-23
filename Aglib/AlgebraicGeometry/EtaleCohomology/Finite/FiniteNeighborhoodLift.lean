/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.StrictLocalOpenStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.LocalDecomposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CoproductSections

/-! # Simultaneous lifts of original geometric neighborhoods on a finite source -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

/-- Every tuple of original sections on the summands glues to an actual section
on their coproduct, with the literal restriction equations. -/
theorem exists_coproduct_section {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale) (F : AbelianSheaf.{u, u + 1} X)
    (a : ∀ i, F.obj.obj (op (U i))) :
    ∃ b : F.obj.obj (op (coproductEtale U)),
      ∀ i, F.obj.map (coproductEtaleInclusion U i).op b = a i := by
  let h := Fan.isLimitMapConeEquiv (CategoryTheory.forget AddCommGrpCat.{u + 1})
    (fun i => F.obj.obj (op (U i))) (disjointSectionsFan F (coproductEtaleInclusion U))
    (isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1})
      (coproductSectionsFanIsLimit U F))
  let a' (i : ι) : PUnit.{u + 2} ⟶
      (CategoryTheory.forget AddCommGrpCat.{u + 1}).obj (F.obj.obj (op (U i))) :=
    TypeCat.ofHom (fun _ => a i)
  refine ⟨Fan.IsLimit.lift h a' PUnit.unit, ?_⟩
  intro i
  exact congrArg (fun k => k PUnit.unit) (Fan.IsLimit.fac h a' i)

variable (A R : Type u) [CommRing A] [CommRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Algebra R A] [Module.Finite R A] {X : Scheme.{u}}

/-- The native residue map, with the local component as its explicit target. -/
def localComponentResidueMap (i : MaximalSpectrum A) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
      localComponents A i := LocalRing.residueSpecMap (Localization.AtPrime i.asIdeal)

include R in
omit [IsSepClosed (IsLocalRing.ResidueField R)] in
/-- A tuple of pointed neighborhoods of the component residue fields lifts to
one map from the whole finite source to their actual coproduct over the base. -/
theorem exists_finite_pointed_neighborhood_lift (f : Spec (.of A) ⟶ X)
    (U : MaximalSpectrum A → X.Etale)
    (t : ∀ i : MaximalSpectrum A,
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (ht : ∀ i : MaximalSpectrum A, t i ≫ (U i).hom =
      localComponentResidueMap A i ≫
        (localComponentInclusion A i ≫ f)) :
    ∃ s : Spec (.of A) ⟶ (coproductEtale U).left,
      s ≫ (coproductEtale U).hom = f ∧
        ∀ i : MaximalSpectrum A, (localComponentResidueMap A i ≫
          localComponentInclusion A i) ≫ s =
            t i ≫ Sigma.ι (fun i => (U i).left) i := by
  have hlocal (i : MaximalSpectrum A) :=
    HenselianLocalRing.henselian_localizationAtPrime R A i.asIdeal
  have hetale (i : MaximalSpectrum A) : Etale (U i).hom := (U i).prop
  choose s hs hred using fun i : MaximalSpectrum A => exists_strictLocal_pointed_lift
    (Localization.AtPrime i.asIdeal) (localComponentInclusion A i ≫ f)
      (U i).hom (t i) (ht i)
  let a := Sigma.desc (fun i => s i ≫ Sigma.ι (fun i => (U i).left) i)
  have ha (i : MaximalSpectrum A) :
      localComponentInclusion A i ≫ (localDecompositionIso A R).inv ≫ a =
        s i ≫ Sigma.ι (fun i => (U i).left) i := by
    rw [← ι_localDecompositionMap A i]
    change (Sigma.ι _ i ≫ (localDecompositionIso A R).hom) ≫
      (localDecompositionIso A R).inv ≫ a = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, a, Sigma.ι_comp_desc]
  refine ⟨(localDecompositionIso A R).inv ≫ a, ?_, ?_⟩
  · have hwhole : a ≫ (coproductEtale U).hom = (localDecompositionIso A R).hom ≫ f := by
      apply Sigma.hom_ext
      intro i
      exact (Category.assoc (Sigma.ι (localComponents A) i) a
        (coproductEtale U).hom).symm.trans
        ((congrArg (fun k : localComponents A i ⟶ (coproductEtale U).left =>
          k ≫ (coproductEtale U).hom) (Sigma.ι_comp_desc
            (fun j => s j ≫ Sigma.ι (fun j => (U j).left) j) i)).trans
          ((Category.assoc (s i) (Sigma.ι (fun j => (U j).left) i)
            (coproductEtale U).hom).trans
            ((congrArg (fun k : (U i).left ⟶ X => s i ≫ k)
              (Sigma.ι_comp_desc (fun j => (U j).hom) i)).trans
              ((hs i).trans (ι_localDecompositionMap_assoc A i f).symm))))
    exact (Category.assoc (localDecompositionIso A R).inv a (coproductEtale U).hom).trans
      ((congrArg (fun k : (∐ localComponents A) ⟶ X =>
        (localDecompositionIso A R).inv ≫ k) hwhole).trans
          ((localDecompositionIso A R).inv_hom_id_assoc f))
  · intro i
    exact (Category.assoc (localComponentResidueMap A i) (localComponentInclusion A i)
      ((localDecompositionIso A R).inv ≫ a)).trans
      ((congrArg (fun k : localComponents A i ⟶ (coproductEtale U).left =>
        localComponentResidueMap A i ≫ k) (ha i)).trans
        ((Category.assoc (localComponentResidueMap A i) (s i)
          (Sigma.ι (fun j => (U j).left) i)).symm.trans
          (congrArg (fun k : Spec (.of (IsLocalRing.ResidueField
            (Localization.AtPrime i.asIdeal))) ⟶ (U i).left =>
              k ≫ Sigma.ι (fun j => (U j).left) i) (hred i))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
