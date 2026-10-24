/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric

/-!
# Perfect pulled-back pairings

Tensoring on the right with a line bundle is fully faithful (`Invertible.tensorRightFullyFaithful`;
it is an equivalence, with inverse tensoring by the dual, `lineBundleDualTensorEquivalence`).
Hence, for an isomorphism `ε : N ⊗ L ⟶ 𝒪_P` with `L` a line bundle and any `p : X ⟶ P`, the maps
`j : M ⟶ p^* N` correspond bijectively to the maps `M ⊗ p^* L ⟶ 𝒪_X` through
`j ↦ pullbackPairingOf p ε j = (j ⊗ 𝟙) ≫ pullbackPairing p ε` (`bijective_pullbackPairingOf`,
`pullbackPairingOfEquiv`).

For `ε` the evaluation pairing `L ⊗ L^∨ ⟶ 𝒪` of a line bundle, this identifies maps
`M ⟶ L_T` with maps `M ⊗ L^∨_T ⟶ 𝒪`, the correspondence between a section `σ` of `L ⊗ f^* N` and
the map `(L ⊗ f^* N)^∨ ⟶ 𝒪` whose image is the ideal of the zero scheme of `σ` (Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, 3.1 and the proof of Thm 3.13, pp. 22 and 25–26; Stacks
Project, Tag 02OQ, Definition 31.15.8). Arbitrary schemes and module sheaves.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring on the right with a line bundle is fully faithful. -/
def Invertible.tensorRightFullyFaithful {X : Scheme.{u}} (B : Invertible.LineBundle X) :
    (tensorRight (show X.Modules from B.val)).FullyFaithful :=
  (Invertible.lineBundleDualTensorEquivalence X B).fullyFaithfulInverse.ofIso
    (BraidedCategory.tensorLeftIsoTensorRight (show X.Modules from B.val))

variable {X P : Scheme.{u}} (p : X ⟶ P) {N L : P.Modules}

/-- The pulled-back pairing of an isomorphism is an isomorphism. -/
instance isIso_pullbackPairing
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) [IsIso ε] :
    IsIso (pullbackPairing p ε) := by
  unfold pullbackPairing
  infer_instance

/-- **A perfect pairing gives a bijection on maps**: for an isomorphism `ε : N ⊗ L ⟶ 𝒪_P` with
`L` a line bundle, `j ↦ pullbackPairingOf p ε j` is a bijection from maps `M ⟶ p^* N` to maps
`M ⊗ p^* L ⟶ 𝒪_X`. -/
theorem bijective_pullbackPairingOf
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) [IsIso ε]
    (hL : Invertible.IsLocallyRankOne P L) (M : X.Modules) :
    Function.Bijective (fun j : M ⟶ (pullback p).obj N ↦ pullbackPairingOf p ε j) := by
  let B : Invertible.LineBundle X := Invertible.pullbackLineBundle p ⟨L, hL⟩
  have h1 := (Invertible.tensorRightFullyFaithful B).map_bijective M ((pullback p).obj N)
  have h2 : Function.Bijective (fun φ : (show X.Modules from tensorSheaf X M ((pullback p).obj L)) ⟶
      (show X.Modules from tensorSheaf X ((pullback p).obj N) ((pullback p).obj L)) ↦
        φ ≫ pullbackPairing p ε) :=
    ⟨fun a b h ↦ (cancel_mono (pullbackPairing p ε)).mp h,
      fun c ↦ ⟨c ≫ inv (pullbackPairing p ε), by simp⟩⟩
  exact h2.comp h1

/-- The bijection `bijective_pullbackPairingOf` as an equivalence. -/
def pullbackPairingOfEquiv
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) [IsIso ε]
    (hL : Invertible.IsLocallyRankOne P L) (M : X.Modules) :
    (M ⟶ (pullback p).obj N) ≃
      ((show X.Modules from tensorSheaf X M ((pullback p).obj L)) ⟶
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :=
  Equiv.ofBijective _ (bijective_pullbackPairingOf p ε hL M)

theorem pullbackPairingOfEquiv_apply
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) [IsIso ε]
    (hL : Invertible.IsLocallyRankOne P L) {M : X.Modules} (j : M ⟶ (pullback p).obj N) :
    pullbackPairingOfEquiv p ε hL M j = pullbackPairingOf p ε j :=
  rfl

/-- Naturality of `pullbackPairingOf` in the source: precomposing `j` with `a` precomposes the
pairing with `a ⊗ 𝟙`. -/
theorem pullbackPairingOf_comp
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf))
    {M M' : X.Modules} (a : M' ⟶ M) (j : M ⟶ (pullback p).obj N) :
    pullbackPairingOf p ε (a ≫ j) =
      tensorSheafMap X a (𝟙 ((pullback p).obj L)) ≫ pullbackPairingOf p ε j := by
  simp only [pullbackPairingOf]
  rw [← Category.assoc, tensorSheafMap_comp, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
