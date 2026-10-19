/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.LinearAlong
public import Aglib.AlgebraicGeometry.Cohomology.Projective.LargeTwistBaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.ToSpec

/-!
# Linearity of the transport from the fibre product to `P^n_B`

For `σ : A →+* B`, write `X_B = P^n_A ×_{Spec A} Spec B`. The transport
`baseChangeTwistCohomologyHom σ ι d M q : H^q(X_B, (𝒪(d) ⊗ M)_B) ⟶ H^q(P^n_B, 𝒪_B(d) ⊗ π^* M)`
of `LargeTwistBaseChange` (pullback along `baseChangeIso σ ι`, then `baseChangeTwistIso`) is an
additive bijection. This file shows that it is `B`-linear, for the action of `B` on the
cohomology of `X_B` through `X_B ⟶ Spec B` (the action used by the base-change map
`moduleCohomologyBaseChangeMap`) and on that of `P^n_B` through `toSpec B ι` (the action used in
`FlatOfSections` and `VanishingProjective`), and packages it as a linear equivalence
(`baseChangeTwistCohomologyLinearEquiv`). The two structural ring maps agree through
`baseChangeIso` (`ProjectiveSpace.baseChangeIso_hom_appTop_comp`, in
`ProjectiveSpace/BaseChange/ToSpec`). Kernel checks of declarations mentioning the
fibre product `P^n_A ×_{Spec A} Spec B` cost seconds each here, so the file states one
declaration over it.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The transport to `P^n_B` is a `B`-linear equivalence**:
`baseChangeTwistCohomologyHom σ ι d M q` (pullback along `baseChangeIso σ ι`, then
`baseChangeTwistIso`) as a `B`-linear equivalence
`H^q(X_B, (𝒪(d) ⊗ M)_B) ≃ H^q(P^n_B, 𝒪_B(d) ⊗ π^* M)`, for the action of `B` through
`X_B ⟶ Spec B` on the source and through `toSpec B ι` on the target. Its underlying map agrees
pointwise with `baseChangeTwistCohomologyHom σ ι d M q`, through
`moduleCohomologyPullbackLinearOfEq_apply`. That equality is not proved by `rfl`:
`moduleCohomologyPullbackLinearOfEq` is defined by `subst`. -/
def baseChangeTwistCohomologyLinearEquiv (σ : A →+* B) (ι : Type u) (d : ℤ)
    (M : (ProjectiveSpace A ι).Modules) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
      ((pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom σ)))).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M)) q
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).obj
        ((Scheme.Modules.pullback (map σ ι)).obj M)) q
    Sheaf.H.{u + 1} (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M))) q ≃ₗ[B]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).obj
          ((Scheme.Modules.pullback (map σ ι)).obj M))) q :=
  LinearEquiv.ofBijective
    ((moduleCohomologyMapOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (baseChangeTwistIso σ ι d M).hom q).comp
        (moduleCohomologyPullbackLinearOfEq (baseChangeIso σ ι).hom
          ((pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
          ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
          (baseChangeIso_hom_appTop_comp σ ι)
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M)) q))
    (by
      refine (Function.Bijective.of_comp_iff' (bijective_sheafH_map_of_iso
        (baseChangeTwistIso σ ι d M) q) _).mpr ?_
      have h := moduleCohomologyPullback_bijective (baseChangeIso σ ι).hom
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M)) q
      rw [← funext (moduleCohomologyPullbackLinearOfEq_apply (baseChangeIso σ ι).hom
        ((pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        (baseChangeIso_hom_appTop_comp σ ι) _ q)] at h
      exact h)

end AlgebraicGeometry.Scheme.Cohomology
