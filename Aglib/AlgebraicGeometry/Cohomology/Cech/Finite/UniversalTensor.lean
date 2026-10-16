/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.AlgebraTests
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.IntBaseChange
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Universal tensor exactness above the actual finite-cover bound

Every commutative ring base change identifies the original integer Cech
complex with the actual Cech complex of the pulled coefficient. The same
finite affine-cover bound applies over the new ring, even when it is not
Noetherian. Native square-zero extension tests then give exactness of the
original following tensor degree for every module. Coefficient relative
flatness is not needed for this universal exactness statement.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type u} (U : ι → X.Opens) (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

include e hU hcover

/-- The original scalar-extended integer Cech complex satisfies the same
sharp bound after every ring map, without flatness or Noetherianity. -/
theorem moduleCechIntComplex_extendScalars_isLE {B : Type u} [CommRing B] (σ : R →+* B) :
    CochainComplex.IsLE
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleCechIntComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M)) (n : ℤ) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : (pullback f (Spec.map (CommRingCat.ofHom σ))).IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  let K : CochainComplex (ModuleCat.{u} B) ℤ :=
    moduleCechIntComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (fun i => p ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj M)
  have hK : CochainComplex.IsLE K (n : ℤ) :=
    moduleCechIntComplex_isLE _ _ _ _ n e
      (fun i => (hU i).preimage p) (p.iSup_preimage_eq_top hcover)
  let := hK
  exact CochainComplex.isLE_of_iso (moduleCechIntBaseChangeIso f σ M U hU).symm (n : ℤ)

/-- Above the original finite-cover cutoff, the original two differentials
are exact after every module tensor product. This is proved from actual
all-ring Cech base change and actual finite-cover vanishing. -/
theorem moduleCechIntComplex_universally_lTensor_exact
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Exact
      (((moduleCechIntComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).d
        (n : ℤ) ((n : ℤ) + 1)).hom.lTensor N)
      (((moduleCechIntComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).d
        ((n : ℤ) + 1) ((n : ℤ) + 2)).hom.lTensor N) := by
  let K := moduleCechIntComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let S := K.sc' (n : ℤ) ((n : ℤ) + 1) ((n : ℤ) + 2)
  refine S.universally_lTensor_exact_of_extendScalars_exact ?_ N
  intro B _ σ
  let L := ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K
  have hL : CochainComplex.IsLE L (n : ℤ) :=
    moduleCechIntComplex_extendScalars_isLE f M U n e hU hcover σ
  let := hL
  have hE : L.ExactAt ((n : ℤ) + 1) :=
    CochainComplex.exactAt_of_isLE L (n : ℤ) ((n : ℤ) + 1) (by omega)
  exact (L.exactAt_iff' (n : ℤ) ((n : ℤ) + 1) ((n : ℤ) + 2)
    (by simp) (by simp [add_assoc])).mp hE

end AlgebraicGeometry.Scheme.Cohomology
