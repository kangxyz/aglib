/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.IntegralFibre

/-!
# Zero schemes of fibrewise nonzero line-bundle maps on integral fibres

Let `f : X ⟶ S` be a morphism, `L` a line bundle on `X` and `φ : L ⟶ O_X` a map, that is, a
section of `L^∨` in the sense of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, 3.1,
p. 22 (Stacks Project, Tag 01WY, Definition 31.15.6). The fibrewise regularity of such maps on
integral fibres (`geometricFibreRegular_of_isIntegral_of_fibre_ne_zero`) and the dual map
`sectionContraction` of a section are in `Modules/Invertible/ZeroLocus/IntegralFibre`. Here:

* `mono_and_flat_zeroInclusion_comp_of_geometricallyIntegral`: for `f` flat, locally of finite
  presentation and geometrically integral (`GeometricallyIntegral f`), a map `φ` that is nonzero
  on every geometric fibre is a monomorphism and its zero scheme is flat over `S` (with the
  proved fibrewise criterion `mono_and_flat_zeroInclusion_comp_of_geometricFibreRegular`);
* `isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral`: under the same
  hypotheses the zero scheme of `φ` is a relative effective Cartier divisor of `X/S`
  (Kleiman, Def. 3.3, p. 22; Stacks Project, Tag 062T), its ideal being the image of `φ`,
  isomorphic to `L` (Stacks Project, Tag 02OR, Lemma 31.15.9);
* `isRelativeEffectiveCartier_zeroInclusion_sectionContraction_of_geometricallyIntegral`: the
  divisor conclusion for a section `σ : O ⟶ M` of a line bundle that is nonzero on every
  geometric fibre, through `sectionContraction M σ : M^∨ ⟶ O`.

This is the regularity step of the inverse map in the proof of Kleiman, Thm 3.13, p. 26,
followed by Lemma 3.4. The base `S` is arbitrary (it can be nonreduced and non-Noetherian); no
properness is used.

Consumer: Picard plan row F15 (`LinSys` in the locally free regime).
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
  (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- For a flat, locally finitely presented, geometrically integral morphism, a line-bundle map
to the structure sheaf that is nonzero on every geometric fibre is a monomorphism with flat zero
scheme. -/
theorem mono_and_flat_zeroInclusion_comp_of_geometricallyIntegral [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    (hφ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      (Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ ≠ 0) :
    Mono φ ∧ Flat (zeroInclusion φ ≫ f) :=
  mono_and_flat_zeroInclusion_comp_of_geometricFibreRegular X S f L φ inferInstance
    inferInstance (geometricFibreRegular_of_isIntegral_of_fibre_ne_zero f L φ
      (fun _ _ _ t => isIntegral_pullback_of_geometricallyIntegral f t) hφ)

/-- For a flat, locally finitely presented, geometrically integral morphism, the zero scheme of
a line-bundle map to the structure sheaf that is nonzero on every geometric fibre is a relative
effective Cartier divisor (Kleiman, Thm 3.13, proof, p. 26, with Lemma 3.4, p. 22). -/
theorem isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    (hφ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      (Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ ≠ 0) :
    Scheme.Hom.IsRelativeEffectiveCartier (zeroInclusion φ) f := by
  obtain ⟨hm, hflat⟩ := mono_and_flat_zeroInclusion_comp_of_geometricallyIntegral f L φ hφ
  have := hm
  exact
    { isClosedImmersion := inferInstance
      isLocallyRankOne := (zeroIdealLineBundle L φ).property
      flat := hflat }

/-- For a flat, locally finitely presented, geometrically integral morphism, the zero scheme of
a section of a line bundle that is nonzero on every geometric fibre is a relative effective
Cartier divisor (Kleiman, Thm 3.13, proof, p. 26). -/
theorem isRelativeEffectiveCartier_zeroInclusion_sectionContraction_of_geometricallyIntegral
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f] (M : LineBundle X)
    (σ : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ (show X.Modules from M.val))
    (hσ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      (Scheme.Modules.pullback (Limits.pullback.fst f t)).map σ ≠ 0) :
    Scheme.Hom.IsRelativeEffectiveCartier (zeroInclusion (sectionContraction M σ)) f :=
  isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral f (dualLineBundle X M)
    (sectionContraction M σ)
    (fun K _ _ t => pullback_map_sectionContraction_ne_zero (Limits.pullback.fst f t) M σ (hσ K t))

end AlgebraicGeometry.Scheme.Modules.Invertible
