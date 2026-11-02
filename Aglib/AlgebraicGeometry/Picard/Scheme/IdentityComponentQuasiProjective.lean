/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.IdentityComponent
public import Aglib.AlgebraicGeometry.Picard.Scheme.QuasiProjectiveLevel

/-!
# Quasi-projectivity of the Picard identity component over any field

The actual identity component of a supplied locally Noetherian fppf Picard representative lies
in the Euler-polynomial stratum containing its unit point. That stratum is clopen, so it contains
the whole connected component. Native compactness of the identity component then places its
original inclusion in one H-quasi-projective level.

The hypotheses are a flat, geometrically integral closed subscheme of finite projective space
over a field and a representative locally of finite type. No curve condition, rational point,
explicit Euler polynomial or algebraic closedness is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Group

namespace AlgebraicGeometry.Scheme.RelativePicard

open Strata

variable {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion i] [Flat (i ≫ toSpec k ι)]
  [GeometricallyIntegral (i ≫ toSpec k ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

omit [GeometricallyIntegral (i ≫ toSpec k ι)] in
/-- The whole original inclusion of the Picard identity component lands in one Euler stratum,
chosen internally as a clopen stratum containing its actual unit point. -/
theorem exists_range_identityComponent_subset_opens_eulerCondition :
    letI := picardCommGrpObj (i ≫ toSpec k ι) P R
    ∃ φ : Polynomial ℚ, Set.range (identityComponent P.obj).ι ⊆
      (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) := by
  let := picardCommGrpObj (i ≫ toSpec k ι) P R
  have hunit : Group.unitPoint P.obj ∈
      ⨆ φ, (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) := by
    rw [iSup_opens_eulerCondition (T := P.obj) (R.homEquiv (𝟙 P))]
    trivial
  obtain ⟨φ, hφ⟩ := TopologicalSpace.Opens.mem_iSup.mp hunit
  refine ⟨φ, ?_⟩
  rw [Scheme.Opens.range_ι]
  exact (isClopen_setOf_holdsAt_eulerCondition (T := P.obj)
    (R.homEquiv (𝟙 P)) φ).connectedComponent_subset hφ

include e in
/-- The actual Picard identity component is H-quasi-projective over every ground field.
Its native compact inclusion factors through one quasi-projective Picard level. -/
theorem isHQuasiProjective_picardIdentityComponent_hom :
    IsHQuasiProjective (picardIdentityComponent (i ≫ toSpec k ι) P R).hom := by
  let := picardCommGrpObj (i ≫ toSpec k ι) P R
  obtain ⟨φ, hφ⟩ := exists_range_identityComponent_subset_opens_eulerCondition i e P R
  exact isHQuasiProjective_comp_of_isCompact_range_of_range_subset_eulerCondition i e P R
    (identityComponent P.obj).ι (isCompact_range (identityComponent P.obj).ι.continuous) φ hφ

end AlgebraicGeometry.Scheme.RelativePicard
