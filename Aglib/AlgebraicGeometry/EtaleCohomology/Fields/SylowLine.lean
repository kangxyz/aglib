/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SylowMonodromy
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.PGroupLine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances

/-! # Actual cyclic coefficient lines after prime-to-p field extension

The genuine Sylow restriction supplies p-power monodromy on the actual
pulled-back coefficient cover. Its original invariant section gives a
monomorphism from the constant prime-cyclic sheaf into the original inverse
image, using the native represented-sheaf base-change isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj
open Scheme.FiniteEtale Scheme.EtaleFundamentalGroups
open Scheme.FiniteEtale.FieldGalois.OverRing
open Scheme.FiniteEtale.GroupBaseChange Scheme.FiniteEtale.FiberTorsorActions

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open MarkedCoefficients MarkedComparisonTransport

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

/-- An actual nontrivial finite prime-torsion coefficient group acquires an
actual constant prime-cyclic subobject after a genuine prime-to-p extension. -/
theorem exists_primeTo_field_cyclic_mono
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] [IsSepClosed Ω]
    (H : Grp (Over (Spec (.of E))))
    [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    {p : ℕ} [Fact p.Prime] [Nontrivial (PointModule (basePoint E Ω) H)]
    (hp : ∀ a : PointModule (basePoint E Ω) H, p • a = 0) :
    ∃ M : IntermediateField E Ω, FiniteDimensional E M ∧
      (Module.finrank E M).Coprime p ∧
      ∃ q : ConstantFinite.coefficient (ULift.{u} (ZMod p)) (Spec (.of M)) ⟶
        (inverseImage (Spec.algebraMap E M)).obj (representedSheaf H), Mono q := by
  obtain ⟨M, hfin, hdegree, hM⟩ :=
    exists_primeTo_field_pPower_monodromy E Ω (coefficientCover H) (p := p)
  let := hfin
  let f := Spec.algebraMap E M
  let s := basePoint M Ω
  let H' := baseChangedGroup f H
  have e : PointModule (basePoint E Ω) H ≃+ PointModule s H' := by
    have hc : s ≫ f = basePoint E Ω := basePoint_comp_algebraMap E M Ω
    exact (AddEquiv.cast (M := fun t : Spec (.of Ω) ⟶ Spec (.of E) =>
      PointModule t H) hc.symm).trans (pullbackFiberMulEquiv f s H).toAdditive
  let : Nontrivial (PointModule s H') := e.symm.toEquiv.nontrivial
  have hp' : ∀ a : PointModule s H', p • a = 0 := by
    intro a
    apply e.symm.injective
    rw [map_nsmul, map_zero]
    exact hp (e.symm a)
  let := pointEvaluationAction s H'
  have himage : IsPGroup p
      (MulAction.toPermHom (FiberAutGroup s) (PointModule s H')).range := by
    rintro ⟨g, γ, rfl⟩
    obtain ⟨n, hn⟩ := hM γ
    refine ⟨n, Subtype.ext ?_⟩
    change (MulAction.toPermHom (FiberAutGroup s) (PointModule s H')) γ ^ p ^ n = 1
    rw [← map_pow]
    apply Equiv.ext
    intro a
    have hpow := congrFun
      (map_pow (PreGaloisCategory.autEmbedding (fiberToFinite s)) γ (p ^ n))
      (coefficientCover H')
    have hv : PreGaloisCategory.autEmbedding (fiberToFinite s)
        (γ ^ p ^ n) (coefficientCover H') = 1 := hpow.trans hn
    exact congrArg Additive.ofMul (congrArg (fun k => k.hom a.toMul) hv)
  obtain ⟨q, hq⟩ := exists_cyclic_mono_of_isPGroup_image s H' hp' himage
  let := hq
  exact ⟨M, hfin, hdegree, q ≫ (representedSheafBaseChangeIso f H).inv, inferInstance⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
