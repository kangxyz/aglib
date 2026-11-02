/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.GeometricRepeated
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.DistinctOpen

/-!
# Geometric effective representatives are simple on the original open

Every repeated effective representative factors the original repeated
Abel map, contradicting the defining open complement. This applies over
every algebraically closed field test, including tests whose image over
the ground field is nonclosed. In genus one, an effective degree-one
divisor is directly a single rational point.

The original universal-family class and its degree are explicit inputs to
this comparison lemma. The actual evaluation-family consumer supplies
them by class recovery, rank-one cohomology and Riemann--Roch.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily Divisors Picard Picard.DivisorClass Picard.Degree

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An effective geometric degree-g representative of the original
universal family is simple at every parameter in the actual retained open. -/
theorem effective_divisor_simple_of_mem_rankOneNonRepeatedOpen
    (hg : 0 < coherentGenus k X)
    {K : Type u} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Spec (.of k))
    (D : Divisor (pullback X.hom b)) (heff : ∀ x, 0 ≤ D x)
    (hdeg : degDiv (pullback X.hom b) (pullback.snd X.hom b) D = (coherentGenus k X : ℤ)) :
    letI := picardCommGrpObj X.hom P R
    let Y : FScheme K := Over.mk (pullback.snd X.hom b)
    let hY := curveProperties_baseChange hX K b
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    ∀ (a : Over.mk b ⟶ identityComponentOver P.obj),
      a.left (IsLocalRing.closedPoint K) ∈ rankOneNonRepeatedOpen hX o ho P R →
      classOf _ (RigidifiedPair.map a
        (degreeUniversalPair hX o ho P R (coherentGenus k X))).bundle =
        divisorToPicard Y.left hY.topologicalKrullDim_eq_one.le D →
      ∀ x, D x = 0 ∨ D x = 1 := by
  classical
  let := picardCommGrpObj X.hom P R
  let Y : FScheme K := Over.mk (pullback.snd X.hom b)
  let hY := curveProperties_baseChange hX K b
  let := hY.proper
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  change ∀ (a : Over.mk b ⟶ identityComponentOver P.obj),
    a.left (IsLocalRing.closedPoint K) ∈ rankOneNonRepeatedOpen hX o ho P R →
      classOf (pullback X.hom b) (RigidifiedPair.map a
        (degreeUniversalPair hX o ho P R (coherentGenus k X))).bundle =
        divisorToPicard Y.left hY.topologicalKrullDim_eq_one.le D →
      ∀ x, D x = 0 ∨ D x = 1
  intro a ha hclass
  by_cases h1 : coherentGenus k X = 1
  · have hdegone : degDiv (pullback X.hom b) (pullback.snd X.hom b) D = (1 : ℤ) :=
      hdeg.trans (congrArg (fun m : ℕ => (m : ℤ)) h1)
    obtain ⟨s, hs⟩ := effective_divisor_eq_sum_points Y.left Y.hom 1 D heff hdegone
    have hD : D = Finsupp.single (s 0) 1 := by simpa only [Fin.sum_univ_one] using hs
    intro x
    by_cases hx : x = s 0
    · exact Or.inr (by rw [hD, hx, Finsupp.single_eq_same])
    · exact Or.inl (by rw [hD, Finsupp.single_eq_of_ne hx])
  · have hg2 : 2 ≤ coherentGenus k X := by omega
    let n := coherentGenus k X - 2
    have hn : n + 2 = coherentGenus k X := by dsimp only [n]; omega
    by_contra hsimple
    have hrep : ∃ x, 2 ≤ D x := by
      by_contra! h
      apply hsimple
      intro x
      have := h x
      have := heff x
      omega
    have hdeg' : degDiv (pullback X.hom b) (pullback.snd X.hom b) D = ((n + 2 : ℕ) : ℤ) :=
      hdeg.trans (congrArg (fun m : ℕ => (m : ℤ)) hn.symm)
    have hclass' : classOf (pullback X.hom b) (RigidifiedPair.map a
        (degreeUniversalPair hX o ho P R (n + 2))).bundle =
        divisorToPicard Y.left hY.topologicalKrullDim_eq_one.le D := by
      exact (congrArg (fun d : ℕ => classOf (pullback X.hom b)
        (RigidifiedPair.map a (degreeUniversalPair hX o ho P R d)).bundle) hn).trans hclass
    obtain ⟨q, hq⟩ := exists_comp_repeatedAbelMorphism_of_effective_divisor
      hX o ho P R (K := K) b n D heff hdeg' hrep a hclass'
    have hnot := (rankOneNonRepeatedOpen_le_nonRepeated hX o ho P R hg2) ha
    change a.left (IsLocalRing.closedPoint K) ∉
      Set.range (repeatedAbelMorphism o ho hX P R n).left at hnot
    exact hnot ⟨q.left (IsLocalRing.closedPoint K),
      congrArg (fun f : Over.mk b ⟶ identityComponentOver P.obj =>
        f.left (IsLocalRing.closedPoint K)) hq⟩

end AlgebraicGeometry.Scheme.OverField.Curve
