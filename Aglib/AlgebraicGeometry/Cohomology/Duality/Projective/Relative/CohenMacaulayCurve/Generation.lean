/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Coefficients.Serre
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Enlargement
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Tensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Basic

/-!
# Coefficient canonical comparisons for curve generation

The actual coefficient Serre map supplies the Hom/H1 comparison and its
trace equation required by finite-support enlargement. In particular the
own-homology canonical sheaf has no nonzero coherent finite-support
subobject. This is not yet global generation: regular hyperplane sections,
their quotient dimensions and the local Nakayama step remain necessary.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem coefficientFiniteSupport_tensor {C : Scheme.{u}} (L T : C.Modules)
    (hT : CanonicalEnlargement.HasFiniteClosedSupport T) :
    CanonicalEnlargement.HasFiniteClosedSupport (L ⊗ T) := by
  obtain ⟨n, p, hp, hc, hz⟩ := hT
  refine ⟨n, p, hp, hc, fun x hx => ?_⟩
  have hTzero : IsZero ((moduleStalk C x).obj T) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact (AddCommGrpCat.isZero_iff_subsingleton).mp (hz x hx)
  have hzero : IsZero ((moduleStalk C x).obj (L ⊗ T)) :=
    ((tensorLeft ((moduleStalk C x).obj L)).map_isZero hTzero).of_iso
      (moduleTensorStalkIso C x L T)
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact (ModuleCat.isZero_iff_subsingleton).mp hzero

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : ModuleCat.{u} k) [Module.Finite k V] (hV : Module.finrank k V = 1)
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (hn : 1 ≤ n)

/-- The actual degree-zero Serre map, on ordinary coherent-source morphisms. -/
def cmCurveCoefficientHomH1Equiv (F : C.Modules)
    (hF : affineLocallyFiniteType C F) :
    (F ⟶ cmCurveCoefficientCanonicalModule k ι j n V) ≃
      (cmCurveSerreCohomology k ι j F 1 →ₗ[k] V) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  exact (Ext.homEquiv₀ (X := F)
    (Y := cmCurveCoefficientCanonicalModule k ι j n V)).symm.trans
    (cmCurveCoefficientSerreDuality k ι j n e V hV hCM F hF 0 (by omega) hn).toEquiv

/-- Its forward formula is the same coefficient trace of the original H1 map. -/
theorem cmCurveCoefficientHomH1Equiv_apply (F : C.Modules)
    (hF : affineLocallyFiniteType C F)
    (f : F ⟶ cmCurveCoefficientCanonicalModule k ι j n V)
    (x : cmCurveSerreCohomology k ι j F 1) :
    cmCurveCoefficientHomH1Equiv k ι j n e V hV hCM hn F hF f x =
      cmCurveCoefficientSerreTrace k ι j n e V hV hCM hn
        ((moduleCohomologyFunctorOfHom C (cmCurveSerreScalar k ι j) 1).map f x) := by
  exact cmCurveCoefficientSerreDuality_zero k ι j n e V hV hCM F hF hn f x

include e hV hCM hn in
/-- The actual coefficient canonical sheaf has no nonzero coherent
finite-closed-support subobject, even when the curve is nonreduced. -/
theorem cmCurveCoefficientCanonical_no_finiteSupport_subobject
    (T : C.Modules) (hT : affineLocallyFiniteType C T)
    (hSupp : CanonicalEnlargement.HasFiniteClosedSupport T)
    (t : T ⟶ cmCurveCoefficientCanonicalModule k ι j n V) [Mono t] : IsZero T := by
  exact CanonicalEnlargement.no_finiteSupport_subobject_of_comparison
    k (cmCurveSerreScalar k ι j) V (cmCurveCoefficientCanonicalModule k ι j n V)
    T hSupp (cmCurveCoefficientHomH1Equiv k ι j n e V hV hCM hn T hT) t

include e hV hCM hn in
/-- Tensoring the actual canonical module by any invertible line retains
purity against coherent finite-support subobjects. -/
theorem cmCurveCoefficientCanonical_tensor_no_finiteSupport_subobject
    (L : Invertible.LineBundle C)
    (T : C.Modules) (hT : affineLocallyFiniteType C T)
    (hSupp : CanonicalEnlargement.HasFiniteClosedSupport T)
    (t : T ⟶ L.val ⊗ cmCurveCoefficientCanonicalModule k ι j n V) [Mono t] :
    IsZero T := by
  let E := Invertible.lineBundleDualTensorEquivalence C L
  let W : C.Modules := cmCurveCoefficientCanonicalModule k ι j n V
  let T' := E.functor.obj T
  let D := Invertible.dualLineBundle C L
  have hD : affineLocallyFiniteType C D.val := by
    let : D.val.IsFinitePresentation := Invertible.lineBundle_isFinitePresentation C D
    exact affineLocallyFiniteType_of_finitePresentation D.val
  have hT' : affineLocallyFiniteType C T' :=
    affineLocallyFiniteType_tensor D.val T hD hT
  have hSupp' : CanonicalEnlargement.HasFiniteClosedSupport T' :=
    coefficientFiniteSupport_tensor D.val T hSupp
  let t₀ : T ⟶ E.inverse.obj W := t
  let : Mono t₀ := inferInstanceAs (Mono t)
  let t' : T' ⟶ W := E.functor.map t₀ ≫ E.counitIso.hom.app W
  let : Mono (E.functor.map t₀) := inferInstance
  let : Mono (E.counitIso.hom.app W) := inferInstance
  have hmono : Mono t' := by dsimp only [t']; infer_instance
  let := hmono
  have hz : IsZero T' := cmCurveCoefficientCanonical_no_finiteSupport_subobject
    k ι j n e V hV hCM hn T' hT' hSupp' t'
  exact (E.inverse.map_isZero hz).of_iso (E.unitIso.app T)

end AlgebraicGeometry.Scheme.Cohomology
