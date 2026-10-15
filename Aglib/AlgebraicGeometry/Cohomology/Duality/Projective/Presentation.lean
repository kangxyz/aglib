/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TopMapLift
public import Aglib.AlgebraicGeometry.Cohomology.Projective.RightExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Canonical top duality across an actual quasicoherent presentation

The original Hom row is left exact by native representable-functor kernel preservation.
The original top-cohomology row is right exact by the proved projective cover bound,
so its represented dual row is left exact as well. Native universe lifts retain the
original canonical top maps. Mathlib's native kernel-diagram isomorphism lemma therefore
transfers bijectivity from the two presentation terms to their actual quotient.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- An actual right-exact quasicoherent presentation transfers bijectivity of the original
canonical top Serre maps from both presentation terms to the actual quotient. -/
theorem projectiveTopSerreMap_bijective_of_presentation (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace R ι).Modules) (hS : S.Exact) [Epi S.g]
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₂ : Function.Bijective (projectiveTopSerreMap R ι n e S.X₂))
    (h₁ : Function.Bijective (projectiveTopSerreMap R ι n e S.X₁)) :
    Function.Bijective (projectiveTopSerreMap R ι n e S.X₃) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α n
  let F : (ProjectiveSpace R ι).Modulesᵒᵖ ⥤ AddCommGrpCat.{u} := preadditiveYoneda.obj ω
  let U := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let Y : ModuleCat.{u + 1} R := ModuleCat.of R (ULift.{u + 1} R)
  let G : (ModuleCat.{u + 1} R)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := preadditiveYoneda.obj Y
  let A₀ := S.op.map F
  let A := A₀.map U
  let B := (S.map H).op.map G
  let : Mono S.op.f := inferInstanceAs (Mono S.g.op)
  have hA₀ : A₀.Exact :=
    hS.op.map_of_mono_of_preservesKernel F inferInstance inferInstance
  let : Mono A₀.f := inferInstanceAs (Mono (F.map S.g.op))
  have hA : A.Exact := hA₀.map_of_mono_of_preservesKernel U inferInstance inferInstance
  let : Mono A.f := inferInstanceAs (Mono (U.map A₀.f))
  have hH : (S.map H).Exact := projectiveTopCohomology_exact R ι n e S hS
  let : Epi (H.map S.g) := projectiveTopCohomologyMap_epi_of_epi R ι n e S.g
  let : Mono (S.map H).op.f := inferInstanceAs (Mono (H.map S.g).op)
  have hB : B.Exact :=
    hH.op.map_of_mono_of_preservesKernel G inferInstance inferInstance
  let : Mono B.f := inferInstanceAs (Mono (G.map (H.map S.g).op))
  let τ (M : (ProjectiveSpace R ι).Modules) :
      AddCommGrpCat.of (ULift.{u + 1} (M ⟶ ω)) ⟶ AddCommGrpCat.of (H.obj M ⟶ Y) :=
    AddCommGrpCat.ofHom (projectiveTopSerreLift R ι n e M).toAddMonoidHom
  let φ : A ⟶ B := {
    τ₁ := τ S.X₃
    τ₂ := τ S.X₂
    τ₃ := τ S.X₁
    comm₁₂ := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change H.map S.g ≫ projectiveTopSerreLift R ι n e S.X₃ f =
        projectiveTopSerreLift R ι n e S.X₂ (ULift.up (S.g ≫ f.down))
      exact (projectiveTopSerreLift_naturality R ι n e S.g f).symm
    comm₂₃ := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change H.map S.f ≫ projectiveTopSerreLift R ι n e S.X₂ f =
        projectiveTopSerreLift R ι n e S.X₁ (ULift.up (S.f ≫ f.down))
      exact (projectiveTopSerreLift_naturality R ι n e S.f f).symm }
  have hmid : IsIso φ.τ₂ := (projectiveTopSerreLift_isIso_iff R ι n e S.X₂).mpr h₂
  let : IsIso φ.τ₃ := (projectiveTopSerreLift_isIso_iff R ι n e S.X₁).mpr h₁
  have hleft : IsIso φ.τ₁ :=
    CategoryTheory.Abelian.isIso_of_isIso_of_mono (ShortComplex.mapToComposableArrows φ)
      hA.exact_toComposableArrows hB.exact_toComposableArrows
      (inferInstanceAs (Mono A.f)) (inferInstanceAs (Mono B.f)) hmid
      (inferInstanceAs (Mono φ.τ₃))
  exact (projectiveTopSerreLift_isIso_iff R ι n e S.X₃).mp hleft

end AlgebraicGeometry.Scheme.Cohomology
