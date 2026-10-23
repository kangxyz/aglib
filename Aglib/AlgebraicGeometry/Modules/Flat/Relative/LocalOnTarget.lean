/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec

/-!
# Relative flatness is local on the target, through cartesian squares

For `p : X ⟶ T` and a module `M` on `X`, relative flatness of `M` over `T` can be tested on the
base changes of `p` along open immersions `j : U ⟶ T` covering `T`: if for every such square
`IsPullback k b p j` the pullback `k^* M` is flat over `U`, then `M` is flat over `T`
(`relativeFlat_of_forall_isPullback`). The squares need not be the chosen pullbacks; for instance
`P^n_B ⟶ P^n_A ×_{Spec A} T` over an affine open `Spec B ⊆ T` qualifies. The point-lifting step
`exists_apply_eq_of_isPullback` says that a point of `X` over the image of `j` comes from the top
left corner of the square. This is the counterpart of `relativeFlat_of_isPullback_of_forall_exists`
(`Modules/Flat/Relative/LocalOnBase`) for a module on `X` that is not pulled back from a base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- **Points over the image of the base of a cartesian square lift**: for `IsPullback k b p j`
and a point `x` of `X` with `p x` in the image of `j`, some point of the top left corner maps to
`x` under `k`. -/
theorem exists_apply_eq_of_isPullback {X T U XU : Scheme.{u}} {p : X ⟶ T} {j : U ⟶ T}
    {k : XU ⟶ X} {b : XU ⟶ U} (hsq : IsPullback k b p j) (x : X) (hx : p x ∈ Set.range j) :
    ∃ z : XU, k z = x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x u hu.symm
  refine ⟨hsq.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst, hw₁]

/-- **Relative flatness is local on the target, through cartesian squares**: for `p : X ⟶ T`
and a module `M` on `X`, if every point of `T` lies in the image of an open immersion `j : U ⟶ T`
with a cartesian square `IsPullback k b p j` such that `k^* M` is flat over `U`, then `M` is flat
over `T`. -/
theorem relativeFlat_of_forall_isPullback {X T : Scheme.{u}} (p : X ⟶ T) (M : X.Modules)
    (H : ∀ t : T, ∃ (U : Scheme.{u}) (j : U ⟶ T) (_ : IsOpenImmersion j) (_ : t ∈ Set.range j)
      (XU : Scheme.{u}) (k : XU ⟶ X) (b : XU ⟶ U),
      IsPullback k b p j ∧ relativeFlat b ((Scheme.Modules.pullback k).obj M)) :
    relativeFlat p M := by
  intro x
  obtain ⟨U, j, hj, hx, XU, k, b, hsq, hflat⟩ := H (p x)
  have : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip hj
  obtain ⟨z, rfl⟩ := exists_apply_eq_of_isPullback hsq x hx
  have h₁ := relativeFlat_comp_of_isOpenImmersion b j hflat
  rw [← hsq.w] at h₁
  have h₂ : relativeFlat (k ≫ p) (M.restrict k) :=
    relativeFlat_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback k).app M) h₁
  exact flat_stalk_of_flat_stalk_restrict k p M z (h₂ z)

end AlgebraicGeometry.Scheme.Modules
