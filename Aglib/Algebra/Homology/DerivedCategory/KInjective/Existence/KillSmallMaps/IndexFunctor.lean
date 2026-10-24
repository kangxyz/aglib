/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.KillSmallMaps.AllMaps

/-!
# Functoriality of the actual all-maps coproduct

Postcomposition acts on the original small indices. The resulting native
coproduct map preserves the original evaluation, without replacing its carrier.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ)
  {K L M : CochainComplex C ℤ}

/-- Postcomposition on the actual small set of all maps. -/
def killAllMapsIndexMap (f : K ⟶ L) (s : killAllMapsIndex A K) : killAllMapsIndex A L :=
  ⟨s.1, equivShrink (A s.1 ⟶ L) (killAllMapsEvaluation A K s ≫ f)⟩

@[simp]
lemma killAllMapsEvaluation_indexMap (f : K ⟶ L) (s : killAllMapsIndex A K) :
    killAllMapsEvaluation A L (killAllMapsIndexMap A f s) =
      killAllMapsEvaluation A K s ≫ f := by
  exact (equivShrink (A s.1 ⟶ L)).symm_apply_apply _

@[simp]
lemma killAllMapsIndexMap_id (s : killAllMapsIndex A K) :
    killAllMapsIndexMap A (𝟙 K) s = s := by
  cases s
  simp [killAllMapsIndexMap, killAllMapsEvaluation]

@[simp]
lemma killAllMapsIndexMap_comp (f : K ⟶ L) (g : L ⟶ M) (s : killAllMapsIndex A K) :
    killAllMapsIndexMap A (f ≫ g) s = killAllMapsIndexMap A g (killAllMapsIndexMap A f s) := by
  rcases s with ⟨i, s⟩
  apply congrArg (Sigma.mk i)
  change equivShrink (A i ⟶ M) (killAllMapsEvaluation A K ⟨i, s⟩ ≫ (f ≫ g)) =
    equivShrink (A i ⟶ M)
      (killAllMapsEvaluation A L (killAllMapsIndexMap A f ⟨i, s⟩) ≫ g)
  rw [killAllMapsEvaluation_indexMap, Category.assoc]

/-- The induced map between the original coproducts. -/
def killAllMapsCoproductMap (f : K ⟶ L) :
    ∐ (killAllMapsSources A K) ⟶ ∐ (killAllMapsSources A L) :=
  Sigma.desc (fun s => Sigma.ι (killAllMapsSources A L) (killAllMapsIndexMap A f s))

@[reassoc (attr := simp)]
lemma killAllMapsCoproductMap_ι (f : K ⟶ L) (s : killAllMapsIndex A K) :
    Sigma.ι (killAllMapsSources A K) s ≫ killAllMapsCoproductMap A f =
      Sigma.ι (killAllMapsSources A L) (killAllMapsIndexMap A f s) :=
  Sigma.ι_comp_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma killAllMapsCoproductMap_id (K : CochainComplex C ℤ) :
    killAllMapsCoproductMap A (𝟙 K) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  simp only [killAllMapsCoproductMap_ι, Category.comp_id]
  simpa only [eqToHom_refl, Category.id_comp] using
    Sigma.eqToHom_comp_ι (killAllMapsSources A K) (killAllMapsIndexMap_id A s)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma killAllMapsCoproductMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    killAllMapsCoproductMap A (f ≫ g) =
      killAllMapsCoproductMap A f ≫ killAllMapsCoproductMap A g := by
  apply Sigma.hom_ext
  intro s
  simp only [killAllMapsCoproductMap_ι, killAllMapsCoproductMap_ι_assoc]
  simpa only [eqToHom_refl, Category.id_comp] using
    Sigma.eqToHom_comp_ι (killAllMapsSources A M) (killAllMapsIndexMap_comp A f g s)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation commutes with the actual coproduct map. -/
@[reassoc]
lemma killAllMapsCoproductMap_evaluation (f : K ⟶ L) :
    killAllMapsCoproductMap A f ≫ Sigma.desc (killAllMapsEvaluation A L) =
      Sigma.desc (killAllMapsEvaluation A K) ≫ f := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, killAllMapsCoproductMap_ι,
    Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  exact killAllMapsEvaluation_indexMap A f s

/-- The actual coproduct of all maps, functorially in the target complex. -/
def killAllMapsCoproductFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := ∐ (killAllMapsSources A K)
  map f := killAllMapsCoproductMap A f
  map_id := killAllMapsCoproductMap_id A
  map_comp := killAllMapsCoproductMap_comp A

/-- The original evaluation maps form a natural transformation. -/
def killAllMapsEvaluationNat : killAllMapsCoproductFunctor A ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := Sigma.desc (killAllMapsEvaluation A K)
  naturality _ _ f := killAllMapsCoproductMap_evaluation A f

end CochainComplex
