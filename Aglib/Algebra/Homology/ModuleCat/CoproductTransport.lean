/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.Coproduct
public import Aglib.Algebra.Category.ModuleCat.DirectSumMap
public import Aglib.Algebra.DirectSumTransport

/-!
# Transporting an exact coproduct-complex computation to a functor

All complex and functor presentations are variable in this lemma. Its
hypotheses identify the actual complex inclusions and coefficient maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w a b z

open CategoryTheory CategoryTheory.Limits HomologicalComplex DirectSum

namespace ModuleCat

variable {R : Type (max u v)} [Ring R] {δ : Type v} {κ : Type w}
  {c : ComplexShape κ} {C : Type a} [Category.{b} C]

/-- The specified functor's canonical coproduct map is bijective. This regular
predicate is shared by abstract transport and its concrete specializations. -/
def FunctorCoproductMapBijective
    (F : C ⥤ ModuleCat.{z} R) (M : δ → C) [HasCoproduct M] : Prop :=
  Function.Bijective (functorCoproductMap F M)

/-- Extract bijectivity from the shared canonical-comparison predicate. -/
theorem FunctorCoproductMapBijective.bijective
    (F : C ⥤ ModuleCat.{z} R) (M : δ → C) [HasCoproduct M]
    (h : FunctorCoproductMapBijective F M) :
    Function.Bijective (functorCoproductMap F M) := h

/-- A natural exact coproduct-complex computation proves the original functor
coproduct map bijective, retaining its specified inclusions. -/
theorem functorCoproductMap_bijective_of_complex
    (F : C ⥤ ModuleCat.{z} R) (M : δ → C) [HasCoproduct M]
    (K : δ → HomologicalComplex (ModuleCat.{max u v} R) c)
    (L : HomologicalComplex (ModuleCat.{max u v} R) c)
    (iso : coproductComplex K ≅ L) (q : κ)
    (eᵢ : ∀ i, (K i).homology q ≃ₗ[R] F.obj (M i))
    (e : L.homology q ≃ₗ[R] F.obj (∐ M)) (a : ∀ i, K i ⟶ L)
    (hi : ∀ i, coproductComplexι K i ≫ iso.hom = a i)
    (hn : ∀ i y, e (homologyMap (a i) q y) = F.map (Sigma.ι M i) (eᵢ i y)) :
    FunctorCoproductMapBijective F M := by
  unfold FunctorCoproductMapBijective
  classical
  exact DirectSum.bijective_of_transport eᵢ
    (coproductComplexHomologyLinearEquiv K q)
    (homologyMapIso iso q).toLinearEquiv e
    (fun i => (homologyMap (coproductComplexι K i) q).hom)
    (functorCoproductMap F M)
    (by
      intro i y
      change (homologyMap (coproductComplexι K i) q ≫
        (coproductComplexHomologyIso K q).hom ≫ (coprodIsoDirectSum _).hom) y = _
      rw [coproductComplexι_homologyIso_assoc, ι_coprodIsoDirectSum_hom]
      rfl)
    (by
      intro i y
      change e ((homologyMap (coproductComplexι K i) q ≫ homologyMap iso.hom q) y) = _
      rw [← homologyMap_comp, hi]
      exact (hn i y).trans (functorCoproductMap_lof F M i (eᵢ i y)).symm)

end ModuleCat
