/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteValueOpenFieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteEtaleCoinduction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.ConnectedTrivialization
public import Aglib.AlgebraicGeometry.Curves.FiniteEtaleCompactification

/-! # Original finite-local-system H1 comparison on open curves

A genuine connected finite-etale trivializing refinement is recovered as an
open of its actual generic normalization. Constant comparison on that smooth
proper curve gives comparison on the cover. The original monic-unit/cokernel
sequence then descends H1 surjectivity, with no trace-degree condition. This
is a fixed-coefficient prime-to-characteristic field-extension theorem, not
full smooth base change or local effacement in arbitrary degrees.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteLocallyConstantOpenFieldExtension

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- The unchanged H1 pullback of a fixed genuine finite local system is
bijective on a nonempty open of the specified smooth proper curve, for an
actual positive annihilator invertible over the algebraically closed base. -/
theorem h1Pullback_bijective
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
    (X : FScheme k) (hX : Properties X)
    {U : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]
    (F : AbelianSheaf.{u, u + 1} U) (hF : IsFiniteLocallyConstant F)
    (N : ℕ) (hpos : 0 < N) (hN : KilledBy N F)
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) :
    Function.Bijective (h1Pullback.{u, u + 2, u + 2}
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) F) := by
  refine ⟨h1Pullback_injective_fieldExtension k K (j ≫ X.hom) F hF, ?_⟩
  let : IsIntegral X.left := hX.isIntegral
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x) := fun x =>
    (Scheme.smoothFieldNormality k X.left X.hom (curveProperties_smooth hX) x).2
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let t := finiteEtaleTrivialization F hF
  obtain ⟨Z, _a, hconn, hsurj, ⟨e⟩⟩ := t.exists_connected_refinement
  let : ConnectedSpace Z.obj.left := hconn
  let : Surjective Z.obj.hom := hsurj
  let : Finite t.value := t.finite_value
  let p := Z.obj.hom
  let M : FScheme k := Over.mk
    ((Scheme.FiniteEtale.GenericNormalization.OpenRecovery.genericMap j p).fromNormalization ≫
      X.hom)
  have hM : Properties M :=
    Curve.FiniteEtaleCompactification.normalization_properties k X hX j p
  let i := Scheme.FiniteEtale.GenericNormalization.OpenRecovery.inclusion j p
  have hi : i ≫ M.hom = p ≫ (j ≫ X.hom) := by
    dsimp only [M, Over.mk_hom]
    rw [← Category.assoc,
      Scheme.FiniteEtale.GenericNormalization.OpenRecovery.inclusion_over, Category.assoc]
  have hCover : Function.Surjective (h1Pullback.{u, u + 2, u + 2}
      (pullback.fst (p ≫ (j ≫ X.hom)) (Spec.algebraMap k K))
      ((inverseImage p).obj F)) := by
    have h := FiniteValueOpenFieldExtension.h1Pullback_bijective_of_constantIso
      k K M hM i ((inverseImage p).obj F) t.value e N hpos
      (killedBy_pullback p hN) hk
    exact hi ▸ h.surjective
  let g := pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)
  let p' := Hom.fibreInclusion (j ≫ X.hom) p (Spec.algebraMap k K)
  have H := Hom.fibreInclusion_isPullback (j ≫ X.hom) p (Spec.algebraMap k K)
  let := Scheme.Geometrically.fieldSpec_geometricallyConnected k K
  apply h1Pullback_surjective_of_finiteEtale_cover p p' g
    (pullback.fst (p ≫ (j ≫ X.hom)) (Spec.algebraMap k K)) H F hF
  exact hCover

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteLocallyConstantOpenFieldExtension
