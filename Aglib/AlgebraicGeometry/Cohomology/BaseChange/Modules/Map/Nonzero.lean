/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec

/-! # Nonzero original sections from actual scalar base change

If the original tensor base-change map is invertible and its target is
nontrivial, some original cohomology class has nonzero geometric pullback.
In degree zero the native H0 comparison produces an actual global section
whose original pullback-adjunction section is nonzero. No finite-rank,
flatness, reducedness or geometric hypothesis is needed for this implication.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
  (f : X ⟶ Spec (.of A)) (σ : A →+* B) (M : X.Modules)

/-- An invertible actual tensor base-change map with nontrivial target cannot
annihilate every original geometric cohomology pullback. -/
theorem exists_cohomologyPullback_ne_zero_of_baseChange_isIso (n : ℕ)
    [IsIso (moduleCohomologyBaseChangeMap f σ M n)]
    [Nontrivial (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ)))
        ((Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) n)] :
    ∃ x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n,
      moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M n x ≠ 0 := by
  by_contra! h
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom _ β ((Modules.pullback p).obj M) n
  let C := moduleCohomologyBaseChangeMap f σ M n
  have hz : C = 0 := by
    apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv _ _).injective
    ext x
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
      ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    change moduleCohomologyBaseChangeMap f σ M n ((1 : B) ⊗ₜ[A,σ] x) = 0
    rw [moduleCohomologyBaseChangeMap_one_tmul, h x]
  obtain ⟨z, hz'⟩ := exists_ne (0 : Sheaf.H.{u + 1}
    (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ)))
      ((Modules.pullback p).obj M)) n)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso C).2 z
  apply hz'
  rw [← hx, hz]
  rfl

/-- The original H0 pullback corresponds to the literal adjunction-unit
section, not an independently chosen section map. -/
theorem moduleCohomologyPullback_equiv₀ {Y : Scheme.{u}} (p : Y ⟶ X)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf Y ((Modules.pullback p).obj M)) isTerminalTop
      (moduleCohomologyPullback p M 0 x) =
        ((Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
          (Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop x) := by
  have h := moduleCohomologyMapAlong_equiv₀ p
    ((Modules.pullbackPushforwardAdjunction p).unit.app M) x
  refine h.trans ?_
  simp [pushforwardSectionsIso, modulePushforwardAddSheafIso]
  rfl

/-- Invertible original q=0 base change and nonzero original target H0 give
an actual global section with nonzero actual pullback. -/
theorem exists_section_pullback_ne_zero_of_baseChange_isIso
    [IsIso (moduleCohomologyBaseChangeMap f σ M 0)]
    [Nontrivial (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ)))
        ((Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) 0)] :
    ∃ s : Γ(M, ⊤),
      ((Modules.pullbackPushforwardAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).unit.app M).app ⊤ s ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_cohomologyPullback_ne_zero_of_baseChange_isIso f σ M 0
  refine ⟨Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop x, ?_⟩
  rw [← moduleCohomologyPullback_equiv₀]
  intro hz
  let P := pullback f (Spec.map (CommRingCat.ofHom σ))
  let N : P.Modules :=
    (Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M
  let E : Sheaf.H.{u + 1} (moduleAddSheaf P N) 0 ≃+ Γ(N, ⊤) :=
    Sheaf.H.equiv₀ (moduleAddSheaf P N) isTerminalTop
  apply hx
  apply E.injective
  exact hz.trans E.map_zero.symm

end AlgebraicGeometry.Scheme.Cohomology
