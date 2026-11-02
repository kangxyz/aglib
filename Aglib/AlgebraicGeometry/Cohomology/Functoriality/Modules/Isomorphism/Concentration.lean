/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism

/-! # Concentration through the original cohomology map of an isomorphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Cohomology

/-- Transport degree-zero rank and positive-degree vanishing using the existing
rank law and the bijectivity of the original geometric cohomology map. -/
theorem moduleCohomology_concentration_of_isIso
    {k : Type u} [Field k] {P Y : Scheme.{u}}
    (e : P ⟶ Y) [IsIso e] (b : Y ⟶ Spec (CommRingCat.of k))
    (t : P ⟶ Spec (CommRingCat.of k)) (w : e ≫ b = t)
    (M : Y.Modules) {N : P.Modules} (C : (Scheme.Modules.pullback e).obj M ≅ N)
    (r : ℕ)
    (h : Module.finrank k (moduleCohomology k (Over.mk b) M 0) = r ∧
      ∀ q : ℕ, 0 < q → Subsingleton (moduleCohomology k (Over.mk b) M q)) :
    Module.finrank k (moduleCohomology k (Over.mk t) N 0) = r ∧
      ∀ q : ℕ, 0 < q → Subsingleton (moduleCohomology k (Over.mk t) N q) := by
  refine ⟨?_, ?_⟩
  · have hr := finrank_moduleCohomology_eq_of_isIso e b t w M C 0
    change @Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0) _ _
        (moduleCohomologyModuleOfHom Y (Scheme.constants (Over.mk b)) M 0) =
      @Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf P N) 0) _ _
        (moduleCohomologyModuleOfHom P (Scheme.constants (Over.mk t)) N 0) at hr
    rw [moduleCohomologyModuleOfHom_constants (Over.mk b) M 0,
      moduleCohomologyModuleOfHom_constants (Over.mk t) N 0] at hr
    exact hr.symm.trans h.1
  · intro q hq
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q) := h.2 q hq
    let φ : M ⟶ (Scheme.Modules.pushforward e).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M ≫
        (Scheme.Modules.pushforward e).map C.hom
    let : (Scheme.Modules.pullback e).IsEquivalence :=
      Scheme.Modules.pullback_isEquivalence_of_isIso e
    let : IsIso φ := inferInstanceAs (IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M ≫
        (Scheme.Modules.pushforward e).map C.hom))
    exact (moduleCohomologyMapAlong_bijective e φ q).surjective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
