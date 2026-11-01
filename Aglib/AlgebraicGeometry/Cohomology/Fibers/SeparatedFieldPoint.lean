/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.FieldPoint.Core
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension.Separated

/-! # Field extension comparison for original field-point dimensions -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

section Dimension

variable {K : Type u} [Field K] {Y : Scheme.{u}}

/-- **Field extension.** For `b : Y ⟶ Spec K` quasi-compact and separated, a field map
`σ : K →+* K'` and a quasicoherent `M`, the dimension of `H^q(Y ×_K Spec K', M_{K'})` over `K'`
is that of `H^q(Y, M)` over `K` (flat base change over a field). -/
theorem moduleCohomologyDimension_fieldBaseChange_of_isSeparated
    (b : Y ⟶ Spec (.of K)) [QuasiCompact b] [IsSeparated b]
    {K' : Type u} [Field K'] (σ : K →+* K') (M : Y.Modules)
    [M.IsQuasicoherent] (q : ℕ) :
    moduleCohomologyDimension (pullback.snd b (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst b (Spec.map (CommRingCat.ofHom σ)))).obj M) q =
      moduleCohomologyDimension b M q :=
  moduleCohomology_finrank_fieldBaseChange_of_isSeparated b σ M q

end Dimension

/-- Field extension at an original base point for a quasi-compact separated
morphism. The coefficient is transported through the same actual pasting iso. -/
theorem moduleCohomologyDimension_pullbackMap_of_eq_of_isSeparated
    {X S : Scheme.{u}} (p : X ⟶ S) [QuasiCompact p] [IsSeparated p]
    {K K' : Type u} [Field K] [Field K'] (k : Spec (.of K) ⟶ S)
    (φ : CommRingCat.of K ⟶ CommRingCat.of K') (k' : Spec (.of K') ⟶ S)
    (hk : Spec.map φ ≫ k = k') (M : (pullback p k).Modules) [M.IsQuasicoherent] (q : ℕ) :
    moduleCohomologyDimension (pullback.snd p k')
        ((Scheme.Modules.pullback (pullback.map p k' p k (𝟙 X) (Spec.map φ) (𝟙 S) (by simp)
          (by simp [hk]))).obj M) q =
      moduleCohomologyDimension (pullback.snd p k) M q := by
  subst hk
  rw [← moduleCohomologyDimension_fieldBaseChange_of_isSeparated (pullback.snd p k) φ.hom M q]
  exact (moduleCohomologyDimension_pullback_snd_pullback_snd p k (Spec.map φ) M q).symm

/-- Euler characteristics compare term by term through the same original
field-valued fibre pullback. No finite-dimensionality assumption is added. -/
theorem moduleEulerChar_pullbackMap_of_eq_of_isSeparated
    {X S : Scheme.{u}} (p : X ⟶ S) [QuasiCompact p] [IsSeparated p]
    {K K' : Type u} [Field K] [Field K'] (k : Spec (.of K) ⟶ S)
    (φ : CommRingCat.of K ⟶ CommRingCat.of K') (k' : Spec (.of K') ⟶ S)
    (hk : Spec.map φ ≫ k = k') (M : (pullback p k).Modules) [M.IsQuasicoherent] :
    moduleEulerChar (pullback.snd p k')
        ((Scheme.Modules.pullback (pullback.map p k' p k (𝟙 X) (Spec.map φ) (𝟙 S) (by simp)
          (by simp [hk]))).obj M) = moduleEulerChar (pullback.snd p k) M := by
  unfold moduleEulerChar
  congr 1
  funext q
  rw [moduleCohomologyDimension_pullbackMap_of_eq_of_isSeparated p k φ k' hk M q]

end AlgebraicGeometry.Scheme.Cohomology
