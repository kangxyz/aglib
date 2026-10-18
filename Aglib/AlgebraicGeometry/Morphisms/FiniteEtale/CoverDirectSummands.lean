/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! A mono of actual finite-etale covers is the inclusion of a direct summand.
The complement is the actual complementary clopen subscheme. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.Connectedness

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (forget forgetToScheme)

universe u
variable {X : Scheme.{u}} {Y Z : Scheme.FiniteEtale X}

theorem coverMonoInducesIsoOnDirectSummand (i : Y ⟶ Z) [Mono i] :
    ∃ (W : Scheme.FiniteEtale X) (j : W ⟶ Z), Nonempty (IsColimit (BinaryCofan.mk i j)) := by
  classical
  let : IsOpenImmersion i.hom.left := isOpenImmersion_of_mono i
  have hi := hom_range_isClopen i
  let U : Z.obj.left.Opens := ⟨(Set.range i.hom.left)ᶜ, hi.1.isOpen_compl⟩
  have hU : IsClosed (U : Set Z.obj.left) := hi.2.isClosed_compl
  let W := clopenCover Z U hU
  let j : W ⟶ Z := clopenCoverι Z U hU
  have hcompl : IsCompl i.hom.left.opensRange U := by
    constructor
    · rw [disjoint_iff]
      ext z
      simp [U]
    · rw [codisjoint_iff]
      ext z
      simp [U]
  have hcompl' : IsCompl i.hom.left.opensRange U.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact hcompl
  obtain ⟨hs⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl i.hom.left U.ι hcompl'
  refine ⟨W, j, ⟨?_⟩⟩
  have : ReflectsColimitsOfShape (Discrete WalkingPair) (forgetToScheme X) := by
    dsimp only [forgetToScheme, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget]
    infer_instance
  apply isColimitOfReflectsOfMapIsColimit (forgetToScheme X)
  change IsColimit (BinaryCofan.mk i.hom.left U.ι)
  exact hs

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 53491aad9bc96df6aa54dfcfd9e04ada8a5ef3535a6423b7f2e568e48e11d398.
Definitions, hypotheses and universes are retained modulo native names. -/
