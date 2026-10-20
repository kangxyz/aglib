/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous.Transgression.Naturality

/-!
# Literal finite-coefficient and cone transgression squares

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/Transgression/FiniteNaturality.lean`.
SHA-256: `955470eeb0e9e51a1cc0d2ef0a86ad3fcc4a2848ab0e86f07960a5b412ad27be`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace AddCommGrpCat.MultiplicationCone.Complex

variable {C₀ C₁ C₂ C₃ : Type*}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup C₃]
  (C : Complex C₀ C₁ C₂ C₃)

/-- Literal coefficient reduction on all four terms is a source chain map. -/
def modReductionChainMap (p q : ℕ) : ChainMap (C.modComplex (p * q)) (C.modComplex p) where
  f₀ := ModTerm.reduction C₀ p q
  f₁ := ModTerm.reduction C₁ p q
  f₂ := ModTerm.reduction C₂ p q
  f₃ := ModTerm.reduction C₃ p q
  comm₀ x := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples C₀ (p * q)) x
    rfl
  comm₁ x := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples C₁ (p * q)) x
    rfl
  comm₂ x := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples C₂ (p * q)) x
    rfl

/-- Literal insertion has representative `q • x` in every source term. -/
def modInsertionChainMap (p q : ℕ) : ChainMap (C.modComplex p) (C.modComplex (p * q)) where
  f₀ := ModTerm.insertion C₀ p q
  f₁ := ModTerm.insertion C₁ p q
  f₂ := ModTerm.insertion C₂ p q
  f₃ := ModTerm.insertion C₃ p q
  comm₀ x := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples C₀ p) x
    change ModTerm.mk C₁ (p * q) (q • C.d₀ x) = ModTerm.mk C₁ (p * q) (C.d₀ (q • x))
    rw [map_nsmul C.d₀]
  comm₁ x := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples C₁ p) x
    change ModTerm.mk C₂ (p * q) (q • C.d₁ x) = ModTerm.mk C₂ (p * q) (C.d₁ (q • x))
    rw [map_nsmul C.d₁]
  comm₂ x := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples C₂ p) x
    change ModTerm.mk C₃ (p * q) (q • C.d₂ x) = ModTerm.mk C₃ (p * q) (C.d₂ (q • x))
    rw [map_nsmul C.d₂]

@[simp] theorem modReductionChainMap_onH₁ (p q : ℕ) :
    (C.modReductionChainMap p q).onH₁ = C.modReduction p q := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.modComplex (p * q)).boundary₁.range z
  rfl

@[simp] theorem modInsertionChainMap_onH₁ (p q : ℕ) :
    (C.modInsertionChainMap p q).onH₁ = C.modInsertion p q := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.modComplex p).boundary₁.range z
  rfl

end AddCommGrpCat.MultiplicationCone.Complex

namespace GroupCohomology.ContinuousH1.Transgression

open AddCommGrpCat.MultiplicationCone
open GroupCohomology

variable {G H : Type*} [_root_.Group G] [TopologicalSpace G] [_root_.Group H] [TopologicalSpace H]
variable {B₀ B₁ B₀' B₁' A A' : Type*}
  [AddCommGroup B₀] [TopologicalSpace B₀] [IsTopologicalAddGroup B₀]
  [DistribMulAction G B₀] [ContinuousSMul G B₀]
  [AddCommGroup B₁] [TopologicalSpace B₁] [IsTopologicalAddGroup B₁]
  [DistribMulAction G B₁] [ContinuousSMul G B₁]
  [AddCommGroup B₀'] [TopologicalSpace B₀'] [IsTopologicalAddGroup B₀']
  [DistribMulAction H B₀'] [ContinuousSMul H B₀']
  [AddCommGroup B₁'] [TopologicalSpace B₁'] [IsTopologicalAddGroup B₁']
  [DistribMulAction H B₁'] [ContinuousSMul H B₁']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DistribMulAction H A'] [ContinuousSMul H A']
  {φ : ContinuousMonoidHom H G}
  {d : ContinuousH1.CoefficientMap G B₀ B₁}
  {d' : ContinuousH1.CoefficientMap H B₀' B₁'}
  (u : ClosedMap φ d d')
  (η : ContinuousH1.CoefficientMap G (Kernel d) A)
  (η' : ContinuousH1.CoefficientMap H (Kernel d') A')
  (a : ContinuousH1.PullbackMap (A := A) (B := A') φ)
  (hη : ∀ k : Kernel d, a (η k) = η' (u.onKernel k))

variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup C₃]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup D₃]
  (C : Complex C₀ C₁ C₂ C₃) (D : Complex D₀ D₁ D₂ D₃)

include hη

/-- The cone transgression square uses the actual integral source chain map
and the already proved naturality of the first-component quotient projection. -/
theorem onConeH1_naturality (f : ChainMap C D) (n : ℕ)
    (s : SourceData d (C.modComplex n)) (t : SourceData d' (D.modComplex n))
    (hs : SourceSquare u s t (f.modChainMap n)) (z : C.H₁mod n) :
    a.onH1 (onConeH1 d η C n s z) = onConeH1 d' η' D n t (f.onH₁mod n z) := by
  change a.onH1 (s.transgression η (C.projectMod n z)) =
    t.transgression η' (D.projectMod n (f.onH₁mod n z))
  rw [ChainMap.projectMod_naturality]
  exact s.transgression_naturality_apply t u (f.modChainMap n) hs η η' a hη _

/-- Reduction naturality for the literal mod-source transgression. -/
theorem onModH1_reduction_naturality (p q : ℕ)
    (s : SourceData d (C.modComplex (p * q))) (t : SourceData d' (C.modComplex p))
    (hs : SourceSquare u s t (C.modReductionChainMap p q))
    (z : (C.modComplex (p * q)).H₁) :
    a.onH1 (onModH1 d η C (p * q) s z) =
      onModH1 d' η' C p t (C.modReduction p q z) := by
  simpa only [onModH1, Complex.modReductionChainMap_onH₁] using
    s.transgression_naturality_apply t u (C.modReductionChainMap p q) hs η η' a hη z

/-- Insertion naturality for the literal mod-source transgression. -/
theorem onModH1_insertion_naturality (p q : ℕ)
    (s : SourceData d (C.modComplex p)) (t : SourceData d' (C.modComplex (p * q)))
    (hs : SourceSquare u s t (C.modInsertionChainMap p q))
    (z : (C.modComplex p).H₁) :
    a.onH1 (onModH1 d η C p s z) =
      onModH1 d' η' C (p * q) t (C.modInsertion p q z) := by
  simpa only [onModH1, Complex.modInsertionChainMap_onH₁] using
    s.transgression_naturality_apply t u (C.modInsertionChainMap p q) hs η η' a hη z

/-- The same reduction square for the existing multiplication-cone source. -/
theorem onConeH1_reduction_naturality (p q : ℕ)
    (s : SourceData d (C.modComplex (p * q))) (t : SourceData d' (C.modComplex p))
    (hs : SourceSquare u s t (C.modReductionChainMap p q)) (z : C.H₁mod (p * q)) :
    a.onH1 (onConeH1 d η C (p * q) s z) =
      onConeH1 d' η' C p t (C.reduction p q z) := by
  change a.onH1 (s.transgression η (C.projectMod (p * q) z)) =
    t.transgression η' (C.projectMod p (C.reduction p q z))
  rw [Complex.projectMod_reduction]
  exact onModH1_reduction_naturality u η η' a hη C p q s t hs _

/-- The same insertion square for the existing multiplication-cone source. -/
theorem onConeH1_insertion_naturality (p q : ℕ)
    (s : SourceData d (C.modComplex p)) (t : SourceData d' (C.modComplex (p * q)))
    (hs : SourceSquare u s t (C.modInsertionChainMap p q)) (z : C.H₁mod p) :
    a.onH1 (onConeH1 d η C p s z) =
      onConeH1 d' η' C (p * q) t (C.insertion p q z) := by
  change a.onH1 (s.transgression η (C.projectMod p z)) =
    t.transgression η' (C.projectMod (p * q) (C.insertion p q z))
  rw [Complex.projectMod_insertion]
  exact onModH1_insertion_naturality u η η' a hη C p q s t hs _

end GroupCohomology.ContinuousH1.Transgression
