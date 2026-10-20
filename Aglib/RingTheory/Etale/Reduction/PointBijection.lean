/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.Reduction.PointSpecialization
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Bijective specialization and model operations

Source correspondence: the finite-level specialization slice supporting
`K2-015#lem:k2015-frobenius` in `research/exposes/K2/015/expose.tex`.

The same finite etale model is free over the local base. Both literal
geometric fibre point sets have its rank, so the canonical reduction already
proved injective is bijective. Actual model comorphisms, comultiplication,
counit and antipode commute with this reduction and the same rho square.
An additive equivalence retains the explicit realization of both fibre group
laws by the same model comultiplication.

The good group model, finite etale multiplication kernel and actual elliptic
fibre identifications remain separate geometric inputs.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.Etale.Reduction.PointBijection`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`460efecefed1de9f05539ba5b0ddace7d440dff269df4ac24e324cf6917710e7`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra.Etale.Reduction

section GeometricCardinality

/-- A split finite-etale algebra over a separably closed field has precisely
its dimension many field points, via its product decomposition. -/
theorem finiteEtale_selfPoint_card (F C : Type*) [Field F] [IsSepClosed F]
    [CommRing C] [Algebra F C] [Module.Finite F C] [Algebra.Etale F C] :
    Nat.card (C →ₐ[F] F) = Module.finrank F C := by
  let : IsArtinianRing C := IsArtinianRing.of_finite F C
  let : Fintype (PrimeSpectrum C) := Fintype.ofFinite _
  calc
    Nat.card (C →ₐ[F] F) = Nat.card (PrimeSpectrum C) :=
      Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum F C)
    _ = Module.finrank F (PrimeSpectrum C → F) := by
      simp
    _ = Module.finrank F C :=
      (Algebra.FormallyEtale.equivPiOfIsSepClosed F C).toLinearEquiv.finrank_eq.symm

/-- Each geometric fibre of the same finite free etale model has its rank
many geometric points. The domain is the literal algebra of that model. -/
theorem finiteEtale_geometricPoint_card (R A F : Type*)
    [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A] [Algebra.Etale R A]
    [Field F] [IsSepClosed F] [Algebra R F] :
    Nat.card (A →ₐ[R] F) = Module.finrank R A := by
  calc
    Nat.card (A →ₐ[R] F) = Nat.card ((F ⊗[R] A) →ₐ[F] F) :=
      Nat.card_congr (AlgHom.liftEquiv R F A F)
    _ = Module.finrank F (F ⊗[R] A) := finiteEtale_selfPoint_card F _
    _ = Module.finrank R A := Module.finrank_baseChange

/-- Finite etale over a local base is finite flat, hence free. No DVR or
additional generic/special rank equality is supplied. -/
theorem finiteEtale_free_of_local (R A : Type*) [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    Module.Free R A := Module.free_of_flat_of_isLocalRing

end GeometricCardinality

section ActualReductionBijection
open Valuation.ResidualGalois
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (V : ValuationSubring K) [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]
  (A : Type*) [CommRing A] [Algebra V A] [Module.Finite V A] [Algebra.Etale V A]

omit [IsUltrametricDist K] [CompleteSpace K]
  [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)] in
theorem genericPoint_card : Nat.card (GenericPoints K V A) = Module.finrank V A := by
  let : Module.Free V A := finiteEtale_free_of_local V A
  exact (Nat.card_congr (genericPointEquiv K V A).symm).trans
    (finiteEtale_geometricPoint_card V A (AlgebraicClosure K))

omit [IsUltrametricDist K] [CompleteSpace K]
  [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)] in
theorem specialPoint_card : Nat.card (SpecialPoints K V A) = Module.finrank V A := by
  let : Module.Free V A := finiteEtale_free_of_local V A
  exact (Nat.card_congr (specialPointEquiv K V A).symm).trans
    (finiteEtale_geometricPoint_card V A
      (AlgebraicClosure (IsLocalRing.ResidueField V)))

/-- Bijectivity of the exact reduction map already proved injective from the
idempotent diagonal. Both actual fibre point sets have the same model rank. -/
theorem genericPointReduction_bijective :
    Function.Bijective (genericPointReduction K V A) := by
  apply (genericPointReduction_injective K V A).bijective_of_nat_card_le
  rw [genericPoint_card, specialPoint_card]

/-- The reduction equivalence between geometric generic and special fibre points
of the same finite etale model over the complete valued field base. -/
def genericPointReductionEquiv : GenericPoints K V A ≃ SpecialPoints K V A :=
  Equiv.ofBijective (genericPointReduction K V A) (genericPointReduction_bijective K V A)

end ActualReductionBijection

section ModelOperations

/-- Evaluation of the actual comultiplication comorphism of a group model. -/
def modelPointProduct (R A F : Type*) [CommRing R] [CommRing A] [CommRing F]
    [Algebra R A] [Algebra R F] (Δ : A →ₐ[R] A ⊗[R] A) (f g : A →ₐ[R] F) :
    A →ₐ[R] F := (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp Δ

/-- Evaluation of the actual counit comorphism of a group model. -/
def modelPointUnit (R A F : Type*) [CommRing R] [CommRing A] [CommRing F]
    [Algebra R A] [Algebra R F] (ε : A →ₐ[R] R) : A →ₐ[R] F :=
  (Algebra.ofId R F).comp ε

/-- Evaluation of the actual antipode comorphism of a group model. -/
def modelPointInverse (R A F : Type*) [CommRing R] [CommRing A] [CommRing F]
    [Algebra R A] [Algebra R F] (ι : A →ₐ[R] A) (f : A →ₐ[R] F) : A →ₐ[R] F := f.comp ι

end ModelOperations

section ModelComorphisms
open Valuation.ResidualGalois
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (V : ValuationSubring K) [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]
  {A B : Type*} [CommRing A] [Algebra V A] [Module.Finite V A]
  [CommRing B] [Algebra V B] [Module.Finite V B]

theorem integralPoint_comp (f : A →ₐ[V] AlgebraicClosure K) (φ : B →ₐ[V] A) :
    integralPoint K V B (f.comp φ) = (integralPoint K V A f).comp φ := by
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  change (integralPoint K V B (f.comp φ) b : AlgebraicClosure K) =
    (integralPoint K V A f (φ b) : AlgebraicClosure K)
  simp only [integralPoint_coe, AlgHom.comp_apply]

/-- Every actual model comorphism commutes with the same reduction map. -/
theorem specializePoint_comp (f : A →ₐ[V] AlgebraicClosure K) (φ : B →ₐ[V] A) :
    specializePoint K V B (f.comp φ) = (specializePoint K V A f).comp φ := by
  ext b
  change closureReduction K V (integralPoint K V B (f.comp φ) b) = _
  rw [integralPoint_comp]
  rfl

/-- Evaluation of the product-model coordinate algebra before reduction. -/
theorem integralPoint_tensorLift (f : A →ₐ[V] AlgebraicClosure K)
    (g : B →ₐ[V] AlgebraicClosure K) :
    integralPoint K V (A ⊗[V] B) (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)) =
      Algebra.TensorProduct.lift (integralPoint K V A f) (integralPoint K V B g)
        (fun _ _ => Commute.all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  apply Subtype.ext
  rw [integralPoint_coe]
  simp only [Algebra.TensorProduct.lift_tmul]
  change f a * g b = (integralPoint K V A f a : AlgebraicClosure K) *
    (integralPoint K V B g b : AlgebraicClosure K)
  rw [integralPoint_coe, integralPoint_coe]

theorem specializePoint_tensorLift (f : A →ₐ[V] AlgebraicClosure K)
    (g : B →ₐ[V] AlgebraicClosure K) :
    specializePoint K V (A ⊗[V] B)
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)) =
      Algebra.TensorProduct.lift (specializePoint K V A f) (specializePoint K V B g)
        (fun _ _ => Commute.all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change closureReduction K V
      (integralPoint K V (A ⊗[V] B)
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)) (a ⊗ₜ[V] b)) = _
  rw [integralPoint_tensorLift]
  simp only [Algebra.TensorProduct.lift_tmul, map_mul]
  rfl

/-- Comultiplication evaluation is preserved by reduction of the same model. -/
theorem specializePoint_modelProduct (Δ : A →ₐ[V] A ⊗[V] A)
    (f g : A →ₐ[V] AlgebraicClosure K) :
    specializePoint K V A (modelPointProduct V A (AlgebraicClosure K) Δ f g) =
      modelPointProduct V A (AlgebraicClosure (IsLocalRing.ResidueField V)) Δ
        (specializePoint K V A f) (specializePoint K V A g) := by
  rw [modelPointProduct, specializePoint_comp, specializePoint_tensorLift]
  rfl

theorem specializePoint_ofId :
    specializePoint K V V (Algebra.ofId V (AlgebraicClosure K)) =
      Algebra.ofId V (AlgebraicClosure (IsLocalRing.ResidueField V)) :=
  Subsingleton.elim _ _

/-- Counit evaluation is preserved by reduction of the same model. -/
theorem specializePoint_modelUnit (ε : A →ₐ[V] V) :
    specializePoint K V A (modelPointUnit V A (AlgebraicClosure K) ε) =
      modelPointUnit V A (AlgebraicClosure (IsLocalRing.ResidueField V)) ε := by
  rw [modelPointUnit, specializePoint_comp, specializePoint_ofId]
  rfl

/-- Antipode evaluation is preserved by reduction of the same model. -/
theorem specializePoint_modelInverse (ι : A →ₐ[V] A)
    (f : A →ₐ[V] AlgebraicClosure K) :
    specializePoint K V A (modelPointInverse V A (AlgebraicClosure K) ι f) =
      modelPointInverse V A (AlgebraicClosure (IsLocalRing.ResidueField V)) ι
        (specializePoint K V A f) := specializePoint_comp K V f ι

/-- Pullback of literal generic fibre points along an actual model comorphism. -/
def genericPointPrecompose (φ : B →ₐ[V] A) (f : GenericPoints K V A) : GenericPoints K V B :=
  f.comp (Algebra.TensorProduct.map (AlgHom.id K K) φ)

/-- Pullback of literal special fibre points along the same model comorphism. -/
def specialPointPrecompose (φ : B →ₐ[V] A) (f : SpecialPoints K V A) : SpecialPoints K V B :=
  f.comp (Algebra.TensorProduct.map
    (AlgHom.id (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField V)) φ)

omit [IsUltrametricDist K] [CompleteSpace K]
  [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]
  [Module.Finite V A] [Module.Finite V B] in
theorem genericPointEquiv_symm_precompose (φ : B →ₐ[V] A) (f : GenericPoints K V A) :
    (genericPointEquiv K V B).symm (genericPointPrecompose K V φ f) =
      ((genericPointEquiv K V A).symm f).comp φ := by
  ext b
  simp only [genericPointPrecompose, genericPointEquiv, AlgHom.liftEquiv_symm_apply,
    AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [IsUltrametricDist K] [CompleteSpace K]
  [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]
  [Module.Finite V A] [Module.Finite V B] in
theorem specialPointEquiv_symm_precompose (φ : B →ₐ[V] A) (f : SpecialPoints K V A) :
    (specialPointEquiv K V B).symm (specialPointPrecompose K V φ f) =
      ((specialPointEquiv K V A).symm f).comp φ := by
  ext b
  simp only [specialPointPrecompose, specialPointEquiv, AlgHom.liftEquiv_symm_apply,
    AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Level-morphism naturality on the actual generic/special coordinate rings.
The source map is the given model comorphism, base-changed on both fibres. -/
theorem genericPointReduction_precompose (φ : B →ₐ[V] A) (f : GenericPoints K V A) :
    genericPointReduction K V B (genericPointPrecompose K V φ f) =
      specialPointPrecompose K V φ (genericPointReduction K V A f) := by
  apply (specialPointEquiv K V B).symm.injective
  simp only [genericPointReduction, Equiv.symm_apply_apply,
    genericPointEquiv_symm_precompose, specialPointEquiv_symm_precompose,
    specializePoint_comp]

/-- Generic group operation evaluated through the actual integral-model
comultiplication, via the universal property of the literal generic fibre. -/
def genericModelProduct (Δ : A →ₐ[V] A ⊗[V] A) (f g : GenericPoints K V A) :
    GenericPoints K V A := genericPointEquiv K V A
      (modelPointProduct V A (AlgebraicClosure K) Δ
        ((genericPointEquiv K V A).symm f) ((genericPointEquiv K V A).symm g))

/-- Special group operation evaluated through the same model comultiplication. -/
def specialModelProduct (Δ : A →ₐ[V] A ⊗[V] A) (f g : SpecialPoints K V A) :
    SpecialPoints K V A := specialPointEquiv K V A
      (modelPointProduct V A (AlgebraicClosure (IsLocalRing.ResidueField V)) Δ
        ((specialPointEquiv K V A).symm f) ((specialPointEquiv K V A).symm g))

/-- The generic-fibre point obtained by evaluating the supplied model counit. -/
def genericModelUnit (ε : A →ₐ[V] V) : GenericPoints K V A :=
  genericPointEquiv K V A (modelPointUnit V A (AlgebraicClosure K) ε)

/-- The special-fibre point obtained by evaluating the supplied model counit. -/
def specialModelUnit (ε : A →ₐ[V] V) : SpecialPoints K V A :=
  specialPointEquiv K V A
    (modelPointUnit V A (AlgebraicClosure (IsLocalRing.ResidueField V)) ε)

theorem genericPointReduction_modelProduct (Δ : A →ₐ[V] A ⊗[V] A)
    (f g : GenericPoints K V A) :
    genericPointReduction K V A (genericModelProduct K V Δ f g) =
      specialModelProduct K V Δ (genericPointReduction K V A f)
        (genericPointReduction K V A g) := by
  apply (specialPointEquiv K V A).symm.injective
  simp only [genericPointReduction, genericModelProduct, specialModelProduct,
    Equiv.symm_apply_apply, specializePoint_modelProduct]

theorem genericPointReduction_modelUnit (ε : A →ₐ[V] V) :
    genericPointReduction K V A (genericModelUnit K V ε) = specialModelUnit K V ε := by
  apply (specialPointEquiv K V A).symm.injective
  simp only [genericPointReduction, genericModelUnit, specialModelUnit,
    Equiv.symm_apply_apply, specializePoint_modelUnit]

/-- Antipode naturality on the literal fibre point rings. -/
theorem genericPointReduction_modelInverse (ι : A →ₐ[V] A) (f : GenericPoints K V A) :
    genericPointReduction K V A (genericPointPrecompose K V ι f) =
      specialPointPrecompose K V ι (genericPointReduction K V A f) :=
  genericPointReduction_precompose K V ι f

end ModelComorphisms

section ActualGroupIdentifications
open Valuation.ResidualGalois
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (V : ValuationSubring K) [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]
  (A : Type*) [CommRing A] [Algebra V A] [Module.Finite V A] [Algebra.Etale V A]
  [AddCommGroup (GenericPoints K V A)] [AddCommGroup (SpecialPoints K V A)]

/-- For genuine group-model fibre identifications, the supplied group laws
on the literal point sets are evaluation of the same comultiplication. These
are model-realization inputs, not an assumed specialization or bijection.
Reduction's addition compatibility and bijectivity have been proved above. -/
def genericPointReductionAddEquiv (Δ : A →ₐ[V] A ⊗[V] A)
    (hgeneric : ∀ f g : GenericPoints K V A, f + g = genericModelProduct K V Δ f g)
    (hspecial : ∀ f g : SpecialPoints K V A, f + g = specialModelProduct K V Δ f g) :
    GenericPoints K V A ≃+ SpecialPoints K V A where
  __ := genericPointReductionEquiv K V A
  map_add' f g := by
    change genericPointReduction K V A (f + g) =
      genericPointReduction K V A f + genericPointReduction K V A g
    rw [hgeneric, hspecial]
    exact genericPointReduction_modelProduct K V Δ f g

/-- The constructed additive isomorphism retains the same actual rho square. -/
theorem genericPointReductionAddEquiv_galois (Δ : A →ₐ[V] A ⊗[V] A)
    (hgeneric : ∀ f g : GenericPoints K V A, f + g = genericModelProduct K V Δ f g)
    (hspecial : ∀ f g : SpecialPoints K V A, f + g = specialModelProduct K V Δ f g)
    (g : Field.absoluteGaloisGroup K) (f : GenericPoints K V A) :
    genericPointReductionAddEquiv K V A Δ hgeneric hspecial (genericPointGalois K V A g f) =
      specialPointGalois K V A (absoluteResidue K V g)
        (genericPointReductionAddEquiv K V A Δ hgeneric hspecial f) :=
  genericPointReduction_galois K V A g f

end ActualGroupIdentifications
end Algebra.Etale.Reduction
