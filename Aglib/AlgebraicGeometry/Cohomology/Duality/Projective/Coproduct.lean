/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistDuality
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Coproduct

/-!
# The canonical top Serre map on finite twist coproducts

The original finite-coproduct cohomology comparison, its actual summand inclusions, and
canonical coefficient naturality transfer bijectivity from each twist to the original
finite coproduct. The inverse is the native `Sigma.desc` of the uniquely supplied summand
morphisms. Prescribed sufficiently negative uniform presentations therefore have the
canonical top-duality isomorphism over every commutative base ring.
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
  {I : Type u} [Finite I]

/-- The canonical top Serre map is bijective on an actual finite twist coproduct whenever
it is bijective on each displayed summand. The maps are the original coefficient maps. -/
theorem projectiveTopSerreMap_twistingCoproduct_bijective (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : I → ℤ)
    (h : ∀ a, Function.Bijective (projectiveTopSerreMap R ι n e (twistingSheaf R ι (d a)))) :
    Function.Bijective
      (projectiveTopSerreMap R ι n e (∐ fun a => twistingSheaf R ι (d a))) := by
  classical
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let F : I → (ProjectiveSpace R ι).Modules := fun a => twistingSheaf R ι (d a)
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (∐ F) n
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α n
  constructor
  · intro f g hfg
    apply Sigma.hom_ext
    intro a
    let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι (d a)) n
    apply (h a).injective
    apply LinearMap.ext
    intro x
    rw [projectiveTopSerreMap_naturality, projectiveTopSerreMap_naturality]
    exact LinearMap.congr_fun hfg
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (Sigma.ι F a)) n x)
  · intro φ
    let φa (a : I) : Module.Dual R (H.obj (F a)) := φ.comp (H.map (Sigma.ι F a)).hom
    choose f hf using fun a => (h a).surjective (φa a)
    refine ⟨Sigma.desc f, ?_⟩
    let E := twistingCoproductCohomologyLinearEquiv R ι d n
    have hE (a : I) (x : H.obj (F a)) :
        E.symm (DFinsupp.single a x) =
          Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
            (Sigma.ι F a)) n x := by
      apply E.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (twistingCoproductCohomologyLinearEquiv_inclusion R ι d n a x).symm
    have hpre : (projectiveTopSerreMap R ι n e (∐ F) (Sigma.desc f)).comp E.symm.toLinearMap =
        φ.comp E.symm.toLinearMap := by
      apply DFinsupp.lhom_ext
      intro a x
      let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι (d a)) n
      change projectiveTopSerreMap R ι n e (∐ F) (Sigma.desc f)
          (E.symm (DFinsupp.single a x)) = φ (E.symm (DFinsupp.single a x))
      rw [hE, ← projectiveTopSerreMap_naturality, Sigma.ι_comp_desc]
      exact LinearMap.congr_fun (hf a) x
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hpre (E x)
    change projectiveTopSerreMap R ι n e (∐ F) (Sigma.desc f) (E.symm (E x)) =
      φ (E.symm (E x)) at hx
    rw [E.symm_apply_apply] at hx
    exact hx

/-- Finite coproducts of the proved residue-pair source twists have bijective original
canonical top Serre maps over every commutative base ring. -/
theorem projectiveTopSerreMap_residueTwistCoproduct_bijective (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (m : I → ℕ) :
    Function.Bijective (projectiveTopSerreMap R ι n e
      (∐ fun a => twistingSheaf R ι (-(m a : ℤ) - (Fintype.card ι : ℤ)))) :=
  projectiveTopSerreMap_twistingCoproduct_bijective R ι n e
    (fun a => -(m a : ℤ) - (Fintype.card ι : ℤ))
    (fun a => projectiveTopSerreMap_residueTwist_bijective R ι n e (m a))

/-- The original common-degree source in a sufficiently negative finite presentation has
bijective canonical top duality, with the displayed integer degree unchanged. -/
theorem projectiveTopSerreMap_uniformNegativeCoproduct_bijective (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (N : ℕ) (hN : Fintype.card ι ≤ N) :
    Function.Bijective (projectiveTopSerreMap R ι n e
      (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ)))) := by
  have hdeg : -(N : ℤ) = -((N - Fintype.card ι : ℕ) : ℤ) - (Fintype.card ι : ℤ) := by omega
  rw [hdeg]
  exact projectiveTopSerreMap_residueTwistCoproduct_bijective R ι n e
    (fun _ : I => N - Fintype.card ι)

end AlgebraicGeometry.Scheme.Cohomology
