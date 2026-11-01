/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCommonOpen
public import Aglib.AlgebraicGeometry.Geometrically.Integral.HypersurfaceFractionField
public import Aglib.AlgebraicGeometry.Spec.PrincipalCommonOpen

/-! # A common open in the original family and a cleared hypersurface

The original generic smooth common open is transported through the actual
coefficient-cleared hypersurface comparison and descended along the original
principal cone. The single descended scheme maps openly to both original
families, retaining their structural triangle over the original domain.
This construction does not yet prove geometric integrality of all fibres.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Project a stage open back to its original family, retaining the whole
original structure equation before specializing either family. -/
private theorem original_open_projection
    {S T X V : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b]
    (f : X ⟶ S) (v : V ⟶ T)
    (a : Over.mk v ⟶ (Over.pullback b).obj (Over.mk f)) [IsOpenImmersion a.left] :
    IsOpenImmersion (a.left ≫ pullback.fst f b) ∧
      (a.left ≫ pullback.fst f b) ≫ f = v ≫ b := by
  refine ⟨inferInstance, ?_⟩
  have ha : a.left ≫ pullback.snd f b = v := Over.w a
  calc
    (a.left ≫ pullback.fst f b) ≫ f = a.left ≫ (pullback.fst f b ≫ f) :=
      Category.assoc _ _ _
    _ = a.left ≫ (pullback.snd f b ≫ b) := congrArg (a.left ≫ ·) pullback.condition
    _ = (a.left ≫ pullback.snd f b) ≫ b := (Category.assoc _ _ _).symm
    _ = v ≫ b := congrArg (· ≫ b) ha

/-- A finitely presented original family with smooth geometrically integral
generic fibre has an actual nonempty quasi-compact common open with a
coefficient-cleared hypersurface. The same polynomial has irreducible images
in all fields over one nonzero principal base open. No Noetherian, proper,
perfect-field, or common-open-certificate assumption is used. -/
theorem exists_generic_hypersurface_common_open
    (R K Ω : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n (pullback.snd f (Spec.algebraMap R K))]
    [GeometricallyIntegral (pullback.snd f (Spec.algebraMap R K))] :
    ∃ Q : MvPolynomial (Fin (n + 1)) R, ∃ r : R, r ≠ 0 ∧
      (∀ (L : Type u) [Field L] (φ : R →+* L), φ r ≠ 0 →
        Irreducible (MvPolynomial.map φ Q)) ∧
      ∃ (V : Scheme.{u}) (i : V ⟶ X)
        (j : V ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {Q}))),
        Nonempty V ∧ CompactSpace V ∧ IsOpenImmersion i ∧ IsOpenImmersion j ∧
        i ≫ f = j ≫ Spec.algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {Q}) := by
  let g := Spec.algebraMap R K
  let fK := pullback.snd f g
  obtain ⟨U, hU, _, s, _, P, hP, jP, hW, hjP, hjPw⟩ :=
    exists_smooth_hypersurface_common_open K Ω fK n
  let W := Spec (.of (Localization.Away s))
  let : Nonempty W := hW
  let iK : W ⟶ pullback f g :=
    Spec.algebraMap Γ(pullback f g, U) (Localization.Away s) ≫ hU.fromSpec
  let w : W ⟶ Spec (.of K) := iK ≫ fK
  let : IsOpenImmersion jP := hjP
  obtain ⟨_, _, Q, _, r, hr, _, hall, e, he⟩ :=
    Hypersurface.exists_cleared_generic_iso R K Ω P hP
  let A := MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {Q}
  let q := Spec.algebraMap R A
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton Q)
  let : LocallyOfFinitePresentation q :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let jK : W ⟶ pullback q g := jP ≫ e.inv
  have heinv : e.inv ≫ pullback.snd q g =
      Spec.algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {P}) := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hjKw : jK ≫ pullback.snd q g = w := by
    change (jP ≫ e.inv) ≫ pullback.snd q g = w
    rw [Category.assoc, heinv]
    simpa only [w, iK, Category.assoc] using hjPw
  let family : Bool → Scheme.{u} := Bool.rec X (Spec (.of A))
  let maps : ∀ b, family b ⟶ Spec (.of R) := Bool.rec f q
  have hfp (b : Bool) : LocallyOfFinitePresentation (maps b) := by
    cases b <;> dsimp only [maps] <;> infer_instance
  have hqc (b : Bool) : QuasiCompact (maps b) := by
    cases b <;> dsimp only [maps, q] <;> infer_instance
  have hqs (b : Bool) : QuasiSeparated (maps b) := by
    cases b <;> dsimp only [maps, q] <;> infer_instance
  let m : ∀ b, Over.mk w ⟶ (Over.pullback g).obj (Over.mk (maps b)) :=
    Bool.rec (Over.homMk iK rfl) (Over.homMk jK hjKw)
  have hm (b : Bool) : IsOpenImmersion (m b).left := by
    cases b
    · change IsOpenImmersion iK
      dsimp only [iK]
      infer_instance
    · change IsOpenImmersion (jP ≫ e.inv)
      infer_instance
  obtain ⟨k, N, hN⟩ := @PrincipalNeighborhoodLimit.exists_common_open_with_comparison
    R _ (nonZeroDivisors R) K _ _ _ family maps hfp hqc hqs W _ w m hm
  obtain ⟨aX, haX, _⟩ := hN false
  obtain ⟨aQ, haQ, _⟩ := hN true
  let b := (PrincipalNeighborhoodLimit.baseStructure (nonZeroDivisors R)).app k.left
  let : IsOpenImmersion b := by
    change IsOpenImmersion (Spec.algebraMap R
      (IsLocalization.PrincipalDiagram.stage (nonZeroDivisors R) k.left.unop))
    infer_instance
  let : IsOpenImmersion aX.left := haX
  let : IsOpenImmersion aQ.left := haQ
  have hX := original_open_projection b f N.f aX
  have hQ := original_open_projection b q N.f aQ
  let : Nonempty N.X := Nonempty.map N.p inferInstance
  let : CompactSpace ((PrincipalNeighborhoodLimit.specDiagram (nonZeroDivisors R)).obj
      k.left) := by
    change CompactSpace (Spec (.of
      (IsLocalization.PrincipalDiagram.stage (nonZeroDivisors R) k.left.unop)))
    infer_instance
  let : CompactSpace N.X := QuasiCompact.compactSpace_of_compactSpace N.f
  exact ⟨Q, r, hr, hall, N.X, aX.left ≫ pullback.fst f b,
    aQ.left ≫ pullback.fst q b, inferInstance, inferInstance, hX.1, hQ.1, hX.2.trans hQ.2.symm⟩

end AlgebraicGeometry.Scheme
