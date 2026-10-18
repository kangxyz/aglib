/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal
public import Aglib.AlgebraicGeometry.Modules.Locality.Monomorphisms
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The finite open-cover coefficient sequence for relative Serre duality

The original restriction units embed a module in the finite biproduct of its
open direct images. On each cover member, the corresponding projection and
original restriction counit give a retraction. The original cokernel sequence
therefore remains short exact after the differential coefficient functor for
any scheme morphism, without assuming that morphism flat.

Quasi-compactness of the finitely many open inclusions ensures that the middle
term and cokernel are quasicoherent. This is the actual coefficient sequence
used by the affine-cover argument; no quotient functor or chosen resolution is
part of its interface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- Pullback followed by tensor with the actual top differential sheaf is additive. -/
instance relativeTopDifferentialCoefficientsFunctor_additive {X Y : Scheme.{u}}
    (p : X ⟶ Y) (n : ℕ) : (relativeTopDifferentialCoefficientsFunctor p n).Additive := by
  change (Scheme.Modules.pullback p ⋙ moduleTensorLeftFunctor X
    (moduleExteriorPower X (Differentials.relativeDifferentialSheaf p) n)).Additive
  infer_instance

variable {Y : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → Y.Opens)

omit [Finite ι] in
private def coverTerms (N : Y.Modules) (i : ι) : Y.Modules :=
  (Scheme.Modules.pushforward (U i).ι).obj (N.restrict (U i).ι)

private def coverUnit (N : Y.Modules) : N ⟶ biproduct (coverTerms U N) := by
  classical
  exact biproduct.lift (fun i => (Scheme.Modules.restrictAdjunction (U i).ι).unit.app N)

private def coverRetraction (N : Y.Modules) (i : ι) :
    (biproduct (coverTerms U N)).restrict (U i).ι ⟶ N.restrict (U i).ι := by
  classical
  exact (Scheme.Modules.restrictFunctor (U i).ι).map (biproduct.π (coverTerms U N) i) ≫
    (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (N.restrict (U i).ι)

private theorem coverUnit_retraction (N : Y.Modules) (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (coverUnit U N) ≫
      coverRetraction U N i = 𝟙 (N.restrict (U i).ι) := by
  classical
  dsimp only [coverUnit, coverRetraction]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, biproduct.lift_π,
    Adjunction.left_triangle_components]

omit [Finite ι] in
private theorem coverPoints (hU : iSup U = ⊤) :
    ∀ y : Y, ∃ (i : ι) (z : (U i).toScheme), (U i).ι z = y := by
  intro y
  have hy : y ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact ⟨i, ⟨y, hi⟩, rfl⟩

private theorem coverUnit_mono (hU : iSup U = ⊤) (N : Y.Modules) :
    Mono (coverUnit U N) := by
  apply Scheme.Modules.mono_of_restrict_openCover
    (fun i => (U i).toScheme) (fun i => (U i).ι) (coverPoints U hU)
  intro i
  have h := coverUnit_retraction U N i
  have : Mono ((Scheme.Modules.restrictFunctor (U i).ι).map (coverUnit U N) ≫
      coverRetraction U N i) := by rw [h]; infer_instance
  exact mono_of_mono _ (coverRetraction U N i)

private theorem coverMiddle_quasicoherent [∀ i, QuasiCompact (U i).ι]
    (N : Y.Modules) [N.IsQuasicoherent] : (biproduct (coverTerms U N)).IsQuasicoherent := by
  classical
  let : ∀ i, (coverTerms U N i).IsQuasicoherent := fun i =>
    Scheme.Modules.QuasiCoherent.quasicoherent_pushforward_open (U i).ι
      (N.restrict (U i).ι)
  apply (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_isLimit
    (biproduct.isLimit (coverTerms U N))
  intro i
  change (coverTerms U N i.as).IsQuasicoherent
  infer_instance

private theorem differentialCoefficients_coverSequence_shortExact
    {X : Scheme.{u}} (p : X ⟶ Y) (n : ℕ) (hU : iSup U = ⊤) (N : Y.Modules)
    (hS : (ShortComplex.cokernelSequence (coverUnit U N)).ShortExact) :
    ((ShortComplex.cokernelSequence (coverUnit U N)).map
      (relativeTopDifferentialCoefficientsFunctor p n)).ShortExact := by
  classical
  let S := ShortComplex.cokernelSequence (coverUnit U N)
  let V : ι → X.Opens := fun i => p ⁻¹ᵁ U i
  have hV : iSup V = ⊤ := p.iSup_preimage_eq_top hU
  apply Scheme.Modules.shortExact_of_restrict_openCover
    (fun i => (V i).toScheme) (fun i => (V i).ι) (coverPoints V hV)
  intro i
  let j := (U i).ι
  let a := (V i).ι
  let q := p ∣_ U i
  let R := Scheme.Modules.restrictFunctor j
  let T := relativeTopDifferentialCoefficientsFunctor q n
  let Sj := S.map R
  have hSj : Sj.ShortExact := hS.map_of_exact R
  let r : Sj.X₂ ⟶ Sj.X₁ := coverRetraction U N i
  have hr : Sj.f ≫ r = 𝟙 Sj.X₁ := coverUnit_retraction U N i
  let splitting := ShortComplex.Splitting.ofExactOfRetraction Sj hSj.exact r hr hSj.epi_g
  let e : (S.map (relativeTopDifferentialCoefficientsFunctor p n)).map
      (Scheme.Modules.restrictFunctor a) ≅ Sj.map T :=
    S.mapNatIso (relativeTopDifferentialCoefficientsRestrictionIso p a q j
      (morphismRestrict_ι p (U i)).symm n)
  exact ShortComplex.shortExact_of_iso e.symm (splitting.map T).shortExact

/-- The original finite open-cover units and their actual cokernel form a quasicoherent
short exact sequence which stays short exact under actual differential coefficients.
No flatness of the scheme morphism or coefficient is needed. -/
theorem exists_shortExact_finiteOpenCover_differentialCoefficients
    {X : Scheme.{u}} (p : X ⟶ Y) (n : ℕ) [∀ i, QuasiCompact (U i).ι]
    (hU : iSup U = ⊤) (N : Y.Modules) [N.IsQuasicoherent] :
    let C := biproduct (fun i =>
      (Scheme.Modules.pushforward (U i).ι).obj (N.restrict (U i).ι))
    ∃ (Q : Y.Modules) (f : N ⟶ C) (g : C ⟶ Q) (h : f ≫ g = 0),
      C.IsQuasicoherent ∧ Q.IsQuasicoherent ∧
      (ShortComplex.mk f g h).ShortExact ∧
      ((ShortComplex.mk f g h).map (relativeTopDifferentialCoefficientsFunctor p n)).ShortExact ∧
      ∀ i, f ≫ biproduct.π
        (fun k => (Scheme.Modules.pushforward (U k).ι).obj (N.restrict (U k).ι)) i =
          (Scheme.Modules.restrictAdjunction (U i).ι).unit.app N := by
  classical
  dsimp only
  let f := coverUnit U N
  let Q := cokernel f
  let g := cokernel.π f
  let hC := coverMiddle_quasicoherent U N
  let hQ : Q.IsQuasicoherent := Scheme.Modules.QuasiCoherent.quasicoherent_cokernel f
  let : Mono f := coverUnit_mono U hU N
  have hS : (ShortComplex.cokernelSequence f).ShortExact := {
    exact := ShortComplex.cokernelSequence_exact f
    mono_f := by change Mono f; infer_instance
    epi_g := by change Epi (cokernel.π f); infer_instance }
  have hT := differentialCoefficients_coverSequence_shortExact U p n hU N hS
  refine ⟨Q, f, g, cokernel.condition f, hC, hQ, hS, hT, ?_⟩
  intro i
  exact biproduct.lift_π _ i

end AlgebraicGeometry.Scheme.Cohomology
