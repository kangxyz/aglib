/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Coproducts.Localization
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Basic

/-! # Coproduct preservation by the actual finite-dimensional unbounded functor

The ordinary functor and its original higher derived functors preserve the
specified coefficient coproducts. Finite-dimensional computation makes the
original derived unit invertible on the coproduct of the same K-injective
replacements. Its naturality transports the actual colimiting cofan.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe s s' u v w u' v' w' t

namespace CategoryTheory.Functor

private def isColimit_mapCocone_of_unit
    {A B J : Type*} [Category* A] [Category* B] [Category* J]
    {L L' : A ⥤ B} (α : L ⟶ L') {K : J ⥤ A} (c : Cocone K)
    [∀ j, IsIso (α.app (K.obj j))] [IsIso (α.app c.pt)]
    (hc : IsColimit (L.mapCocone c)) : IsColimit (L'.mapCocone c) := by
  let e : K ⋙ L ≅ K ⋙ L' := NatIso.ofComponents (fun j => asIso (α.app (K.obj j)))
    (by intro i j f; exact α.naturality (K.map f))
  refine IsColimit.precomposeHomEquiv e (L'.mapCocone c) ?_
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (asIso (α.app c.pt)) ?_
  intro j
  exact α.naturality (c.ι.app j)

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [IsGrothendieckAbelian.{s'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  {κ : Type t} [HasColimitsOfShape (Discrete κ) C] [HasColimitsOfShape (Discrete κ) D]
  [PreservesColimitsOfShape (Discrete κ) F]
  [∀ n : ℕ, PreservesColimitsOfShape (Discrete κ) (F.rightDerived (n + 1))]
  (N : ℕ) (hbound : ∀ M : C, IsZero ((F.rightDerived (N + 1)).obj M))

include N hbound in
/-- The actual derived image of the original localized coproduct cofan is
colimiting for a family of acyclic-term complexes. -/
theorem unboundedRightDerived_preservesColimit_of_acyclic_terms
    (K : κ → CochainComplex C ℤ)
    (hK : ∀ a i n, IsZero ((F.rightDerived (n + 1)).obj ((K a).X i))) :
    PreservesColimit (Discrete.functor K ⋙ DerivedCategory.Q)
      F.unboundedRightDerivedFunctor := by
  have hsum (i : ℤ) (n : ℕ) : IsZero ((F.rightDerived (n + 1)).obj ((∐ K).X i)) := by
    let G := F.rightDerived (n + 1)
    let e : G.obj ((∐ K).X i) ≅ ∐ fun a => G.obj ((K a).X i) :=
      G.mapIso (PreservesCoproduct.iso (eval C (.up ℤ) i) K) ≪≫
        PreservesCoproduct.iso G (fun a => (K a).X i)
    apply e.isZero_iff.mpr
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro a
    exact (hK a i n).eq_of_src _ _
  let : ∀ a : Discrete κ, IsIso
      (F.unboundedRightDerivedFunctorUnit.app ((Discrete.functor K).obj a)) :=
    fun a => F.isIso_unboundedRightDerivedFunctorUnit_app_of_acyclic_terms
      N hbound (K a.as) (hK a.as)
  let c := Cofan.mk (∐ K) (Sigma.ι K)
  let : IsIso (F.unboundedRightDerivedFunctorUnit.app c.pt) :=
    F.isIso_unboundedRightDerivedFunctorUnit_app_of_acyclic_terms N hbound (∐ K) hsum
  have hc := isColimitOfPreserves
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (coproductIsCoproduct K)
  have hg := isColimit_mapCocone_of_unit F.unboundedRightDerivedFunctorUnit c hc
  exact preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves DerivedCategory.Q (coproductIsCoproduct K)) hg

include N hbound in
/-- The original unbounded derived functor preserves the specified arbitrary
coproducts, proved using the same actual K-injective replacement of each summand. -/
theorem unboundedRightDerived_preservesCoproducts_of_bound :
    PreservesColimitsOfShape (Discrete κ) F.unboundedRightDerivedFunctor := by
  constructor
  intro G
  let K (a : κ) := DerivedCategory.Q.objPreimage (G.obj ⟨a⟩)
  let I (a : κ) :=
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C)).obj (K a)
  let η (a : κ) :=
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C)).app (K a)
  let e : Discrete.functor I ⋙ DerivedCategory.Q ≅ G := Discrete.natIso (fun a =>
    (asIso (DerivedCategory.Q.map (η a.as))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (G.obj a))
  have : PreservesColimit (Discrete.functor I ⋙ DerivedCategory.Q)
      F.unboundedRightDerivedFunctor :=
    F.unboundedRightDerived_preservesColimit_of_acyclic_terms N hbound I
      (fun a i n => F.isZero_rightDerived_obj_injective_succ n _)
  exact preservesColimit_of_iso_diagram F.unboundedRightDerivedFunctor e

end CategoryTheory.Functor
