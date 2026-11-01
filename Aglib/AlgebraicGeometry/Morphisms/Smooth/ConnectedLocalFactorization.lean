/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.PointedAffineEtaleComponent
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.PointedChartBaseChange
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Pointed connected local factorization of a smooth morphism

The original standard affine chart, the genuine etale section neighborhood,
and its actual section-component open combine inside the original pullback.
No global quasi-compactness or quasi-separatedness of the smooth family or
its base is required. The etale neighborhood of the arbitrary base is not
asserted to be globally of finite presentation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

/-- Every point of a smooth family of displayed relative dimension belongs
to an original open in an etale base change whose structural morphism is
smooth, qcqs and geometrically connected. The second projection is etale and
retains the prescribed point; the original square commutes literally. -/
theorem exists_connected_local_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : S.Etale) (W : (pullback V.hom f : Scheme.{u}).Opens)
      (w : W.toScheme),
      IsAffine V.left ∧ (W.ι ≫ pullback.snd V.hom f) w = x ∧
      SmoothOfRelativeDimension n (W.ι ≫ pullback.fst V.hom f) ∧
      QuasiCompact (W.ι ≫ pullback.fst V.hom f) ∧
      QuasiSeparated (W.ι ≫ pullback.fst V.hom f) ∧
      GeometricallyConnected (W.ι ≫ pullback.fst V.hom f) ∧
      UniversallyOpen (W.ι ≫ pullback.fst V.hom f) ∧
      Etale (W.ι ≫ pullback.snd V.hom f) ∧
      (W.ι ≫ pullback.fst V.hom f) ≫ V.hom =
        (W.ι ≫ pullback.snd V.hom f) ≫ f := by
  obtain ⟨U, hU, A, hA, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (f := f) (n := n) x
  let R := Γ(S, U)
  let B := Γ(X, A)
  let : Algebra R B := (f.appLE U A e).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n R B :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp hstd
  let f₀ : Spec (.of B) ⟶ Spec (.of R) := Spec.algebraMap R B
  let i : Spec (.of B) ⟶ X := hA.fromSpec
  let j : Spec (.of R) ⟶ S := hU.fromSpec
  have h : f₀ ≫ j = i ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f hU hA e
  let xB : Spec (.of B) := hA.isoSpec.hom ⟨x, hx⟩
  have hxB : i xB = x := by
    change (hA.isoSpec.hom ≫ hA.fromSpec) ⟨x, hx⟩ = x
    rw [hA.isoSpec_hom_fromSpec]
    rfl
  obtain ⟨T, hT, hRT, het, ε, y, hyx, hy⟩ :=
    exists_pointed_affine_etale_section_component R B n xB
  let : CommRing T := hT
  let : Algebra R T := hRT
  let c : Spec (.of T) ⟶ Spec (.of R) := Spec.algebraMap R T
  let : Etale c := (HasRingHomProperty.Spec_iff (P := @Etale.{u})).mpr
    (RingHom.etale_algebraMap.mpr het)
  let : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion hA.fromSpec)
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  let V : S.Etale := Etale.mk (c ≫ j)
  obtain ⟨A₀, _, hA₀, _, _, hsm, hqc, hqs, hgc, _⟩ :=
    exists_standardBaseChangeSection_restriction R B T n ε
  have hya : y ∈ A₀ := by
    change y ∈ (A₀ : Set (pullback f₀ c : Scheme.{u}))
    rw [hA₀]
    exact hy
  let a : A₀.toScheme := ⟨y, hya⟩
  let : SmoothOfRelativeDimension n (A₀.ι ≫ pullback.snd f₀ c) := hsm
  let : QuasiCompact (A₀.ι ≫ pullback.snd f₀ c) := hqc
  let : QuasiSeparated (A₀.ι ≫ pullback.snd f₀ c) := hqs
  let : GeometricallyConnected (A₀.ι ≫ pullback.snd f₀ c) := hgc
  have hax : (A₀.ι ≫ pullback.fst f₀ c ≫ i) a = x := by
    change i (pullback.fst f₀ c y) = x
    rw [hyx]
    exact hxB
  obtain ⟨W, w, _, _, hw, hsmW, hqcW, hqsW, hgcW⟩ :=
    exists_pointedChart_open_image f f₀ i j h c A₀ n a x hax
  let : SmoothOfRelativeDimension n (W.ι ≫ pullback.fst (c ≫ j) f) := hsmW
  let : Smooth (W.ι ≫ pullback.fst (c ≫ j) f) :=
    SmoothOfRelativeDimension.smooth n _
  refine ⟨V, W, w, ?_, hw, hsmW, hqcW, hqsW, hgcW, ?_, ?_, ?_⟩
  · change IsAffine (Spec (.of T))
    infer_instance
  · change UniversallyOpen (W.ι ≫ pullback.fst (c ≫ j) f)
    infer_instance
  · change Etale (W.ι ≫ pullback.snd (c ≫ j) f)
    infer_instance
  · simp only [Category.assoc, pullback.condition]

end AlgebraicGeometry.Scheme
