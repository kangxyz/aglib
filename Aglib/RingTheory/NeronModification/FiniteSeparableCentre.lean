/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.RationalSquare
public import Aglib.RingTheory.DiscreteValuationRing.FiniteOpenRationalization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Localization

/-! # Original strict improvement at a finite separable residue centre

The auxiliary DVR square, principal open, rational residue point, extended
centre identity and target point are all constructed by finite-open
rationalization. Strict improvement descends to the original modification.
No domain hypothesis is required on the original finite-type algebra.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace Algebra.NeronModification

variable (R E S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]
  (e : E →ₐ[ResidueField R] ResidueField S)

/-- The coefficient ring acts on the specified finite separable residue
extension through its original residue map. -/
local instance finiteSeparableCentreResidueAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

/-- The constructed residue-extension base acts on its actual target through
`SeparableResidueExtension.targetMap`. -/
local instance finiteSeparableCentreTargetAlgebra :
    Algebra (SeparableResidueExtension.Ring R E) (SeparableResidueExtension.TargetRing R E S e) :=
  (SeparableResidueExtension.targetMap R E S e).toRingHom.toAlgebra

local instance finiteSeparableCentreTargetTower :
    IsScalarTower R (SeparableResidueExtension.Ring R E)
      (SeparableResidueExtension.TargetRing R E S e) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (SeparableResidueExtension.targetMap R E S e).commutes r |>.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B ι : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Finite ι]

/-- Finite separability of the actual centre residue field gives a strict step
on the original algebra and original target DVR, at the original fixed index. -/
theorem exists_lift_fittingIdeal_lt_of_finiteSeparableCentre
    (p : R) (g : ι → B) (χ : B →ₐ[R] S) (f : B →ₐ[R] E)
    (hpR : Irreducible p) (hpS : Irreducible (algebraMap R S p))
    (hf : Function.Surjective f) (hres : ∀ b, residue S (χ b) = e (f b))
    (hcentre : Ideal.span (insert (algebraMap R B p) (Set.range g)) = RingHom.ker f.toRingHom)
    (k : ℕ)
    (hne : (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom ≠ ⊥)
    (hproper : (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom ≠ ⊤) :
    ∃ χM : Modification (algebraMap R B p) g →ₐ[R] S,
      (∀ b, χM (of (algebraMap R B p) g b) = χ b) ∧
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom <
        (Module.fittingIdeal _
          (KaehlerDifferential R (Modification (algebraMap R B p) g)) k).map χM.toRingHom := by
  obtain ⟨s, hs, hfinite, _, hker, hres'⟩ :=
    SeparableResidueExtension.exists_finite_open_rationalization R E S e f χ hf hres
  let A := SeparableResidueExtension.Ring R E
  let T := Localization.Away s
  let U := SeparableResidueExtension.TargetRing R E S e
  let : Algebra.FiniteType A T := hfinite
  let : Algebra.FormallyEtale B T := inferInstance
  let : Module.Flat B T := Module.Flat.trans B (B ⊗[R] A) T
  let χT := SeparableResidueExtension.openTargetPoint R E S e f χ s hs hres
  let φ := SeparableResidueExtension.openRationalPoint R E f s hs
  let σ : S →ₐ[R] U := IsScalarTower.toAlgHom R S U
  have hpA : maximalIdeal A = Ideal.span {algebraMap R A p} :=
    (SeparableResidueExtension.irreducible_algebraMap R E hpR).maximalIdeal_eq
  have hpU : Irreducible (algebraMap R U p) := by
    rw [IsScalarTower.algebraMap_apply R S U]
    exact SeparableResidueExtension.target_irreducible_algebraMap R E S e hpS
  have hpoint (b : B) : χT (algebraMap B T b) = σ (χ b) := by
    rw [IsScalarTower.algebraMap_apply B (B ⊗[R] A) T]
    change χT (algebraMap (B ⊗[R] A) T (b ⊗ₜ[R] (1 : A))) = σ (χ b)
    change SeparableResidueExtension.openTargetPoint R E S e f χ s hs hres
      (algebraMap (B ⊗[R] A) T (b ⊗ₜ[R] (1 : A))) = _
    rw [SeparableResidueExtension.openTargetPoint_tmul, map_one, mul_one]
    rfl
  have hcentreT : RingHom.ker φ.toRingHom =
      (Ideal.span (insert (algebraMap R B p) (Set.range g))).map (algebraMap B T) := by
    rw [hcentre]
    rw [hker]
    change ((RingHom.ker f.toRingHom).map (algebraMap B (B ⊗[R] A))).map
      (algebraMap (B ⊗[R] A) T) = (RingHom.ker f.toRingHom).map (algebraMap B T)
    rw [Ideal.map_map]
    congr 1
  have hg (i : ι) : residue S (χ (g i)) = 0 := by
    rw [hres]
    have hi : g i ∈ RingHom.ker f.toRingHom := by
      rw [← hcentre]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    rw [show f (g i) = 0 from hi, map_zero]
  exact exists_lift_fittingIdeal_lt_of_rationalSquare p g χ χT σ hpA hpS hpU hpoint φ
    (ResidueField.map (SeparableResidueExtension.targetMap R E S e).toRingHom)
    hres' hcentreT hg k hne hproper

end Algebra.NeronModification
