/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.AffineExtension
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.AffineSystem
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.SystemTransport

/-!
# Absolute arithmetic approximation of quasi-compact quasi-separated schemes

Finite affine-cover induction applies the constructed one-affine extension theorem.
Each open union is retained literally through its native restriction coordinates, and the
final top-open isomorphism returns the original scheme as the actual limiting cone point.
No approximation-system or extension existence hypothesis is part of the endpoint.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

/-- Every compact open of a quasi-separated scheme has an actual arithmetic system. -/
theorem nonempty_system_compactOpen {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : Nonempty (System U.toScheme) := by
  refine compact_open_induction_on U hU ?_ ?_
  · have : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
    exact ⟨affineSystem (⊥ : X.Opens).toScheme⟩
  · intro S hS V ih
    obtain ⟨M⟩ := ih
    let T : X.Opens := S ⊔ V.val
    have : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp
      (hS.union V.property.isCompact)
    have : QuasiSeparatedSpace T.toScheme := quasiSeparatedSpace_of_quasiSeparated T.ι
    let U' : T.toScheme.Opens := T.ι ⁻¹ᵁ V.val
    let V' : T.toScheme.Opens := T.ι ⁻¹ᵁ S
    have hU' : IsAffineOpen U' := V.property.preimage_of_isOpenImmersion T.ι (by
      simpa only [Opens.opensRange_ι] using (le_sup_right : V.val ≤ T))
    have hV' : IsCompact (V' : Set T.toScheme) := T.ι.isCompact_preimage hS
    have hcover : U' ⊔ V' = ⊤ := by
      change (T.ι ⁻¹ᵁ V.val) ⊔ (T.ι ⁻¹ᵁ S) = ⊤
      rw [← Hom.preimage_sup, sup_comm V.val S]
      exact T.ι_preimage_self
    let e : V'.toScheme ≅ S.toScheme := T.ι.isoImage V' ≪≫ X.isoOfEq (by
      change T.ι ''ᵁ (T.ι ⁻¹ᵁ S) = S
      rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
        inf_eq_right.mpr (le_sup_left : S ≤ T)])
    exact nonempty_system_of_affine_open_union U' V' hU' hV' hcover (M.ofIso e)

/-- Every quasi-compact quasi-separated scheme is the actual limit of a small cofiltered
arithmetic finite-type system with affine transitions. -/
theorem nonempty_system (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (System X) := by
  obtain ⟨M⟩ := nonempty_system_compactOpen (X := X) ⊤ isCompact_univ
  exact ⟨M.ofIso X.topIso.symm⟩

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
