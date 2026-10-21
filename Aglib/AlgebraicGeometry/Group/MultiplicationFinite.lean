/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CurveIsogeny
public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Nonconstant pointed curve maps and actual multiplication

A pointed map of smooth proper geometrically connected curve groups is dominant
and finite if it differs from the constant map to the origin. This is proved for
the original morphism, using the dimension-one generic-point dichotomy and
faithful scalar extension to an algebraic closure.

For the literal multiplication map `(𝟙 G.X) ^ n`, the remaining hypothesis is
explicitly that this morphism is not the constant map. The first-order proof in
`Group.MultiplicationCotangent` supplies this condition when `n` is invertible
in the base field; this leaf retains the general nonconstancy interface.

Target correspondence: the finite conjunct of `EllipticMultiplicationGeometry`,
`R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean`,
lines 283–286 of the frozen R5Lab packet at `f8a3314ddecffcada2ec721d26d56a937bed9690`.
The target theorem family is not an input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

/-- Over an algebraically closed field, a pointed curve map different from the
constant origin map is dominant. No finiteness or differential input is used. -/
theorem pointed_nonconstant_isDominant_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G.X ⟶ H.X)
    (hp : η[G.X] ≫ f = η[H.X]) (hne : f ≠ 1) : IsDominant f.left := by
  let := hG.isIntegral
  let := hH.isIntegral
  let := hG.proper
  let := hH.proper
  let : LocallyOfFiniteType (f.left ≫ H.X.hom) := by
    rw [f.w]
    infer_instance
  rcases DimensionOne.point_eq_generic_or_isClosed H.X.left
      (le_of_eq (curveProperties_dimension Scheme.smoothFieldDimension hH))
      (f.left (genericPoint G.X.left)) with hgen | hclosed
  · refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure H.X.left]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint G.X.left, hgen⟩)
  · exfalso
    apply hne
    apply Over.OverMorphism.ext
    apply ext_of_apply_eq H.X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    · intro x _ _
      have hc (z : G.X.left) : f.left z = f.left (genericPoint G.X.left) := by
        have hz := specializes_iff_mem_closure.mp
          ((genericPoint_specializes z).map f.left.continuous)
        rwa [hclosed.closure_eq, Set.mem_singleton_iff] at hz
      have hp' := congrArg
        (fun m : 𝟙_ (FScheme k) ⟶ H.X => m.left (IsLocalRing.closedPoint k)) hp
      calc
        f.left x = f.left (η[G.X].left (IsLocalRing.closedPoint k)) :=
          (hc x).trans (hc _).symm
        _ = η[H.X].left (IsLocalRing.closedPoint k) := hp'
        _ = (1 : G.X ⟶ H.X).left x := by
          simp only [CategoryTheory.Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
          congr 1
          exact @Subsingleton.elim (PrimeSpectrum k) inferInstance _ _
    · exact f.w.trans (1 : G.X ⟶ H.X).w.symm

/-- A pointed map between the actual curve groups is dominant whenever it is
not the constant origin map, over the original arbitrary field. -/
theorem pointed_nonconstant_isDominant
    {k : Type u} [Field k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G.X ⟶ H.X)
    (hp : η[G.X] ≫ f = η[H.X]) (hne : f ≠ 1) : IsDominant f.left := by
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let P := Over.pullback s
  let B := Scheme.Group.BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let H' := B.functor.obj H
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  let : GrpObj (P.obj H.X) := Functor.grpObjObj
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  have hG' : Properties G'.X :=
    { smooth := MorphismProperty.pullback_snd G.X.hom s hG.smooth
      proper := MorphismProperty.pullback_snd G.X.hom s hG.proper
      connected := MorphismProperty.pullback_snd G.X.hom s hG.connected }
  have hH' : Properties H'.X :=
    { smooth := MorphismProperty.pullback_snd H.X.hom s hH.smooth
      proper := MorphismProperty.pullback_snd H.X.hom s hH.proper
      connected := MorphismProperty.pullback_snd H.X.hom s hH.connected }
  have hp' : η[G'.X] ≫ P.map f = η[H'.X] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map η[G.X]) ≫ P.map f =
      Functor.LaxMonoidal.ε P ≫ P.map η[H.X]
    simp only [Category.assoc, ← Functor.map_comp, hp]
  have hne' : P.map f ≠ 1 := by
    intro he
    apply hne
    apply P.map_injective
    rw [Functor.map_one]
    exact he
  let : IsDominant (P.map f).left :=
    pointed_nonconstant_isDominant_of_isAlgClosed G' H' hG' hH' (P.map f) hp' hne'
  have hcomp : (P.map f).left ≫ pullback.fst H.X.hom s =
      pullback.fst G.X.hom s ≫ f.left := by
    simp [P]
  let : IsDominant (pullback.fst G.X.hom s ≫ f.left) := by
    rw [← hcomp]
    infer_instance
  exact IsDominant.of_comp (pullback.fst G.X.hom s) f.left

/-- Nonconstant pointed maps of the original proper curve groups are finite
and surjective. This result is valid in every characteristic. -/
theorem pointed_nonconstant_finite_surjective
    {k : Type u} [Field k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G.X ⟶ H.X)
    (hp : η[G.X] ≫ f = η[H.X]) (hne : f ≠ 1) :
    IsFinite f.left ∧ Surjective f.left := by
  let := pointed_nonconstant_isDominant G H hG hH f hp hne
  let := dominant_isFinite hG hH f
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.Group.Multiplication

open AlgebraicGeometry.Scheme.OverField
attribute [local instance] Over.cartesianMonoidalCategory

/-- The literal multiplication morphism preserves the actual origin. -/
theorem multiplication_pointed {k : Type u} [Field k] (G : Grp (FScheme k)) (n : ℕ) :
    η[G.X] ≫ (𝟙 G.X) ^ n = η[G.X] := by
  rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one]
  exact one_pow n

/-- Nontriviality of the actual multiplication morphism implies finiteness and
surjectivity in every characteristic. The nontriviality premise is explicit. -/
theorem multiplication_finite_surjective_of_ne_one
    {k : Type u} [Field k] (G : Grp (FScheme k)) (hG : Curve.Properties G.X)
    (n : ℕ) (hne : (𝟙 G.X) ^ n ≠ 1) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Surjective ((𝟙 G.X) ^ n).left :=
  Curve.pointed_nonconstant_finite_surjective G G hG hG _ (multiplication_pointed G n) hne

end AlgebraicGeometry.Scheme.Group.Multiplication
