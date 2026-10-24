/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Projective
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.BaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free

/-!
# The zero twist on the fibres of a projective embedding

The twist by `O(0)` is the identity: `pulledTwistZeroIso h M : h^* O(0) ⊗ M ≅ M`, from the actual
zero-twist isomorphism `twistingZeroIso : O(0) ≅ O`, the pullback of the unit
(`Scheme.Modules.pullbackUnitIso`) and the left unitor of the sheafified tensor
(`SheafOfModulesOfCommRing.tensorLeftUnitIso`).

Consequently, for `i : X ⟶ P^N_A`, `g : T ⟶ Spec A` and a module `M` on `X_T = X ×_{Spec A} T`,
the point-fibre cohomology of `M` itself at `t ∈ T` is the twisted fibre cohomology at twist `0`:

* `modulePointFiberCohomologyDimension_eq_embeddedFiberTwistDim_zero`: the point-fibre dimension
  of `M` in degree `q` is `h^q(X_t, O(0) ⊗ M_t)`;
* `subsingleton_modulePointFiberCohomology_iff_embeddedFiberTwistDim_zero`: for a closed
  immersion `i` with `ι ≃ Fin (N + 1)` and a line bundle `L`, the point-fibre cohomology of `L` in
  degree `q` vanishes exactly when `h^q(X_t, O(0) ⊗ L_t) = 0`.

This is the bridge from the fibre conditions of the Picard strata at `m = 0` to the hypotheses of
cohomology and base change for the direct image of `L` (statement 15a of the Picard plan; Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, p. 30: "`H^1(X_t, L_t) = 0` for all `t ∈ T′`").
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u}

/-- **The zero twist is the identity**: `h^* O(0) ⊗ M ≅ M` for `h : Y ⟶ P^N_A`. -/
def pulledTwistZeroIso {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι) (M : Y.Modules) :
    pulledTwist h 0 M ≅ M :=
  (moduleTensorRightFunctor Y M).mapIso
      ((Scheme.Modules.pullback h).mapIso (twistingZeroIso A ι) ≪≫
        Scheme.Modules.pullbackUnitIso h) ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).app M

variable {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι) {T : Scheme.{u}}
  (g : T ⟶ Spec (.of A))

/-- The point-fibre dimension of a module `M` on `X_T` at `t` is `h^q(X_t, O(0) ⊗ M_t)`. -/
theorem modulePointFiberCohomologyDimension_eq_embeddedFiberTwistDim_zero
    (M : (pullback (i ≫ toSpec A ι) g).Modules) (q : ℕ) (t : T) :
    modulePointFiberCohomologyDimension (pullback.snd (i ≫ toSpec A ι) g) M q t =
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj M) 0 q := by
  rw [modulePointFiberCohomologyDimension_congr _
    (pulledTwistZeroIso (pullback.fst (i ≫ toSpec A ι) g ≫ i) M).symm q t]
  exact modulePointFiberCohomologyDimension_pulledTwist i g M 0 q t

-- The first `rw` matches `ringCatSheaf` spelled as a `TopCat.Sheaf` against its use as a site
-- sheaf in `SheafOfModules`, which needs relaxed transparency.
set_option backward.isDefEq.respectTransparency false in
/-- For a closed immersion `i` and a line bundle `L` on `X_T`, the point-fibre cohomology of `L` at
`t` vanishes in degree `q` exactly when `h^q(X_t, O(0) ⊗ L_t) = 0`. -/
theorem subsingleton_modulePointFiberCohomology_iff_embeddedFiberTwistDim_zero
    [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) g)) (q : ℕ) (t : T) :
    Subsingleton (modulePointFiberCohomology (pullback.snd (i ≫ toSpec A ι) g) L.val q t) ↔
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) 0 q =
          0 := by
  rw [subsingleton_modulePointFiberCohomology_iff_pullbackMap,
    embeddedFiberTwistDim_eq_zero_iff i (K := T.residueField t) _ N e _ 0
      (affineLocallyFiniteType_of_isLocallyRankOne (isLocallyRankOne_pulledTwist _ 0
        (Invertible.pullback_locallyRankOne _ _ L.property))) q]
  exact (subsingleton_moduleCohomology_congr (pulledTwistZeroIso _ _) q).symm

end AlgebraicGeometry.Scheme.Cohomology
