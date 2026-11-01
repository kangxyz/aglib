/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIdentity
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange

/-! # Actual raw identity-pullback geometry before normalization -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

universe u
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : DenseCompactification f)

local instance identityRawProjection_isIso : IsIso (pullback.snd (𝟙 S) C.p) :=
  (IsPullback.of_hasPullback (𝟙 S) C.p).isIso_snd_of_isIso

omit [QuasiCompact f] in
/-- The raw identity projection is an actual refinement onto the original
compactification transported along the actual source-pullback isomorphism. -/
theorem identityRawProjection_open :
    (C.toCompactification.baseChange (𝟙 S)).j ≫ pullback.snd (𝟙 S) C.p =
      ((identitySourceTransport f).obj C).j :=
  Compactification.baseChange_j_snd C.toCompactification (𝟙 S)

omit [QuasiCompact f] in
/-- The actual raw identity projection retains the proper map. -/
theorem identityRawProjection_p :
    pullback.snd (𝟙 S) C.p ≫ C.p = pullback.fst (𝟙 S) C.p :=
  pullback.condition.symm.trans (Category.comp_id _)

omit [QuasiCompact f] in
/-- The raw identity projection has the original Cartesian common-source square. -/
theorem isPullback_identityRawProjection_open :
    IsPullback (C.toCompactification.baseChange (𝟙 S)).j
      (𝟙 (pullback (𝟙 S) f)) (pullback.snd (𝟙 S) C.p)
      ((identitySourceTransport f).obj C).j := by
  change IsPullback (C.toCompactification.baseChange (𝟙 S)).j
    (𝟙 (pullback (𝟙 S) f)) (pullback.snd (𝟙 S) C.p)
    ((identitySourceIso f).hom ≫ C.j)
  exact @IsPullback.of_vert_isIso Scheme _
    (pullback (𝟙 S) f) (pullback (𝟙 S) C.p) (pullback (𝟙 S) f) C.Xbar
    (C.toCompactification.baseChange (𝟙 S)).j (𝟙 (pullback (𝟙 S) f))
    (pullback.snd (𝟙 S) C.p) ((identitySourceIso f).hom ≫ C.j)
    (inferInstanceAs (IsIso (𝟙 (pullback (𝟙 S) f))))
    ((IsPullback.of_hasPullback (𝟙 S) C.p).isIso_snd_of_isIso)
    ⟨(identityRawProjection_open C).trans (Category.id_comp _).symm⟩

omit [QuasiCompact f] in
/-- The comparison with the identity ambient refinement is Cartesian with its
actual original projection, not merely an isomorphic replacement. -/
theorem isPullback_identityRawProjection :
    IsPullback (pullback.snd (𝟙 S) C.p) (pullback.snd (𝟙 S) C.p)
      (𝟙 C.Xbar) (𝟙 C.Xbar) :=
  IsPullback.of_horiz_isIso ⟨rfl⟩

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
