/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.PointLocalization
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseOneNonreturn
public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Equiv
public import Aglib.RingTheory.LocalRing.ParameterEquiv

/-!
# Original Case-I selection and fixed-parameter succession

The same point-localization square transports the genuine ordinary-local
successor, including its whole kernel and good binary restriction. The
original point-local-ring map, parameter and residue map are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalCaseOneStep

private theorem map_firstZero {R S : Type*} [CommSemiring R] [CommSemiring S]
    (ρ : R →+* S) (q : MvPolynomial (Fin 3) R) :
    MvPolynomial.map ρ (MvPolynomial.eval₂Hom
      (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q) =
      MvPolynomial.eval₂Hom
        (MvPolynomial.C : S →+* MvPolynomial (Fin 2) S)
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] (MvPolynomial.map ρ q) := by
  have h : (MvPolynomial.map ρ).comp
      (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
        ![0, MvPolynomial.X 0, MvPolynomial.X 1]) =
      (MvPolynomial.eval₂Hom (MvPolynomial.C : S →+* MvPolynomial (Fin 2) S)
        ![0, MvPolynomial.X 0, MvPolynomial.X 1]).comp (MvPolynomial.map ρ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X]
      fin_cases i
      · change (MvPolynomial.map ρ) 0 = 0
        exact map_zero _
      · change (MvPolynomial.map ρ) (MvPolynomial.X 0) = MvPolynomial.X 0
        exact MvPolynomial.map_X ρ 0
      · change (MvPolynomial.map ρ) (MvPolynomial.X 1) = MvPolynomial.X 1
        exact MvPolynomial.map_X ρ 1
  exact RingHom.congr_fun h q

/-- A real next singular point selects a good parameter on the same original
parent stalk. No generic-hyperplane or field-size premise is used. -/
theorem exists_good_parameter
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [IsDomain (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)]
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (y : B.Y) (hy : IsClosed ({y} : Set B.Y)) (hbase : B.map y = x)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y))
    (t : maximalIdeal (X.presheaf.stalk x)) (g : Fin 2 → maximalIdeal (X.presheaf.stalk x))
    (hgen : Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i :
      X.presheaf.stalk x)) = maximalIdeal (X.presheaf.stalk x))
    (q : MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x)))
    (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (hns : ¬ ∃ c : ResidueField (X.presheaf.stalk x), c ≠ 0 ∧
      ∃ L : MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x)),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = MvPolynomial.C c * L ^ 2) :
    let A : Type u := X.presheaf.stalk x
    ∃ (t' : maximalIdeal A) (g' : Fin 2 → maximalIdeal A)
        (q' : MvPolynomial (Fin 3) (ResidueField A)),
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t' g' i : A)) =
        maximalIdeal A ∧ q' ≠ 0 ∧ q'.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap t' g') = Ideal.span {q'} ∧
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' ≠ 0) ∧
      (¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' =
          MvPolynomial.C c * L ^ 2) := by
  let A : Type u := X.presheaf.stalk x
  let D := Arc.pointBlowup A
  obtain ⟨_, _, yD, hyD, hDbase, _, ε, _, _⟩ :=
    PointLocalization.exists_closed_point_stalkIso x hx B y hy hbase
  have hs : ¬ IsRegularLocalRing (D.Y.presheaf.stalk yD) := by
    intro h
    let : IsRegularLocalRing (D.Y.presheaf.stalk yD) := h
    exact hsing (IsRegularLocalRing.of_ringEquiv ε.commRingCatIsoToRingEquiv.symm)
  obtain ⟨t', g', q', hg, hq'0, hq', hk, hr0, hrns, _⟩ :=
    CaseOneNonreturn.exists_good_parameter_of_closed_singular_child
      D t g hgen q hq0 hq hker hns yD hyD hDbase hs
  exact ⟨t', g', q', hg, hq'0, hq', hk, hr0, hrns⟩

/-- A fixed good original parameter persists at the actual original singular
child. Every child cone and nonreturn fact is produced, not supplied. -/
theorem exists_fixed_parameter_successor
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [IsDomain (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdA : ringKrullDim (X.presheaf.stalk x) = 2)
    (hA : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hRat : NormalModificationH1Vanishing (X.presheaf.stalk x))
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (y : B.Y) (hy : IsClosed ({y} : Set B.Y)) (hbase : B.map y = x)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y))
    (t : maximalIdeal (X.presheaf.stalk x)) (g : Fin 2 → maximalIdeal (X.presheaf.stalk x))
    (hgen : Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i :
      X.presheaf.stalk x)) = maximalIdeal (X.presheaf.stalk x))
    (q : MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x)))
    (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (hr0 : MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField (X.presheaf.stalk x) →+*
        MvPolynomial (Fin 2) (ResidueField (X.presheaf.stalk x)))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0)
    (hrns : ¬ ∃ c : ResidueField (X.presheaf.stalk x), c ≠ 0 ∧
      ∃ L : MvPolynomial (Fin 2) (ResidueField (X.presheaf.stalk x)),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
          MvPolynomial.C c * L ^ 2) :
    let A : Type u := X.presheaf.stalk x
    let C : Type u := B.Y.presheaf.stalk y
    let f := (Arc.pointLocalRingMap B.map y x hbase).hom
    ∃ (p : maximalIdeal C) (g' : Fin 2 → maximalIdeal C)
        (q' : MvPolynomial (Fin 3) (ResidueField C)),
      (p : C) = f (t : A) ∧
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators p g' i : C)) =
        maximalIdeal C ∧
      (p : C) ∉ maximalIdeal C ^ 2 ∧
      (maximalIdeal A).map f = Ideal.span {(p : C)} ∧
      Function.Bijective (ResidueField.map f) ∧
      q' ≠ 0 ∧ q'.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {q'} ∧
      (¬ ∃ L : MvPolynomial (Fin 3) (ResidueField C),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {L ^ 2}) ∧
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField C →+* MvPolynomial (Fin 2) (ResidueField C))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' ≠ 0) ∧
      (¬ ∃ c : ResidueField C, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField C),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' =
          MvPolynomial.C c * L ^ 2) ∧
      MvPolynomial.FirstCoordinate.dehom q' ≠ 0 ∧
      (MvPolynomial.FirstCoordinate.dehom q').totalDegree ≤ 2 ∧
      (¬ ∃ c : ResidueField C, c ≠ 0 ∧ ∃ l : CaseOne.Plane C,
        l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q' =
          MvPolynomial.C c * l ^ 2) ∧
      Nonempty (CaseOne.Presentation C p g' (MvPolynomial.FirstCoordinate.dehom q')) := by
  let A : Type u := X.presheaf.stalk x
  let C : Type u := B.Y.presheaf.stalk y
  let f : A →+* C := (Arc.pointLocalRingMap B.map y x hbase).hom
  let : IsLocalHom f := Arc.pointLocalRingMap_isLocal B.map y x hbase
  let D := Arc.pointBlowup A
  obtain ⟨_, _, yD, _, hDbase, _, ε, _, hε⟩ :=
    PointLocalization.exists_closed_point_stalkIso x hx B y hy hbase
  let Y := MaximalIdealBlowup.source A hdA
  let yS : Y := yD
  let S : Type u := Y.presheaf.stalk yS
  let : IsLocalRing S := Y.toLocallyRingedSpace.isLocalRing yS
  let c : A →+* S := (MaximalIdealBlowup.map A hdA).stalkScalar yS
  let : IsLocalHom c :=
    (MaximalIdealBlowup.map A hdA).stalkScalar_isLocalHom_of_closedPoint yS hDbase
  let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
  have he : e.toRingHom.comp f = c := hε
  have hs : ¬ IsRegularLocalRing S := by
    intro h
    let : IsRegularLocalRing S := h
    exact hsing (IsRegularLocalRing.of_ringEquiv e.symm)
  obtain ⟨_, p0, g0, q0, hp0, hgen0, hmin0, hcenter0, hres0,
      hq00, hq0hom, hker0, hnonreturn0, hr00, hrns0, _, _, _, _⟩ :=
    CaseOneNonreturn.exists_ordinary_fixed_parameter_successor_at_singular_point (A := A)
      hdA hA hRat t g hgen q hq0 hq hker hr0 hrns yS hs
  let p : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm p0
  let g' : Fin 2 → maximalIdeal C := fun i => maximalIdealEquivMap e.symm (g0 i)
  let σ : ResidueField S ≃+* ResidueField C := ResidueField.mapEquiv e.symm
  let q' := MvPolynomial.mapEquiv (Fin 3) σ q0
  have hordered : (fun i => maximalIdealEquivMap e.symm (CaseOne.orderedGenerators p0 g0 i)) =
      CaseOne.orderedGenerators p g' := by
    funext i
    fin_cases i <;> rfl
  have hvalues : (fun i => (CaseOne.orderedGenerators p g' i : C)) =
      fun i => e.symm.toRingHom (CaseOne.orderedGenerators p0 g0 i).val := by
    funext i
    exact congrArg Subtype.val (congrFun hordered i).symm
  have hgen' : Ideal.span (Set.range fun i => (CaseOne.orderedGenerators p g' i : C)) =
      maximalIdeal C := by
    have hgen0S : Ideal.span (Set.range fun i =>
        (CaseOne.orderedGenerators (A := S) p0 g0 i).val) = maximalIdeal S := hgen0
    have h := congrArg (Ideal.map e.symm.toRingHom) hgen0S
    rw [Ideal.map_span, ← Set.range_comp'] at h
    have hm := map_maximalIdeal_of_surjective (R := S) (S := C)
      e.symm.toRingHom e.symm.surjective
    rw [hvalues]
    exact h.trans hm
  have hker' : RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {q'} := by
    have h := doubleLineChildCotangentKernel_ringEquiv e.symm
      (CaseOne.orderedGenerators p0 g0)
    have hk : doubleLineChildCotangentKernel S (CaseOne.orderedGenerators p0 g0) =
        Ideal.span {q0} := hker0
    rw [hordered, hk, Ideal.map_span, Set.image_singleton] at h
    exact h
  have hep : e.toRingHom (p : C) = c (t : A) := by
    change e (e.symm p0.val) = c (t : A)
    exact (e.apply_symm_apply _).trans hp0
  have hp0S : p0.val = c (t : A) := hp0
  have hmin0S : p0.val ∉ maximalIdeal S ^ 2 := hmin0
  have hcenter0S : (maximalIdeal A).map c = Ideal.span {p0.val} := hcenter0
  have hminS : c (t : A) ∉ maximalIdeal S ^ 2 := by
    rw [← hp0S]
    exact hmin0S
  have hcenterS : (maximalIdeal A).map c = Ideal.span {c (t : A)} := by
    rw [← hp0S]
    exact hcenter0S
  have htransport := parameter_properties_of_equiv_comp
    (A := A) (R := C) (S := S) f c e he (t : A) (p : C) hep
  have htransport_min := htransport hminS
  have htransport_center := htransport_min hcenterS
  obtain ⟨hp, hmin, hcenter, hres⟩ := htransport_center hres0
  have hq'0 : q' ≠ 0 := by
    intro hz
    exact hq00 ((MvPolynomial.mapEquiv (Fin 3) σ).injective
      (hz.trans (map_zero (MvPolynomial.mapEquiv (Fin 3) σ)).symm))
  have hq' : q'.IsHomogeneous 2 := hq0hom.map σ.toRingHom
  have hback : (fun i => maximalIdealEquivMap e (CaseOne.orderedGenerators p g' i)) =
      CaseOne.orderedGenerators p0 g0 := by
    funext i
    apply Subtype.ext
    have h := congrArg (fun a : maximalIdeal C => e (a : C)) (congrFun hordered i)
    exact h.symm.trans (e.apply_symm_apply _)
  have hnonreturn : ¬ ∃ L : MvPolynomial (Fin 3) (ResidueField C),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {L ^ 2} := by
    rintro ⟨L, hL, hL0, hkL⟩
    have hkL' : doubleLineChildCotangentKernel C (CaseOne.orderedGenerators p g') =
        Ideal.span {L ^ 2} := hkL
    have h := doubleLineChildCotangentKernel_ringEquiv e (CaseOne.orderedGenerators p g')
    rw [hback, hkL', Ideal.map_span, Set.image_singleton, map_pow] at h
    let ψ := MvPolynomial.mapEquiv (Fin 3) (ResidueField.mapEquiv e)
    have hψL : ψ L ≠ 0 := by
      intro hz
      exact hL0 (ψ.injective (hz.trans (map_zero ψ).symm))
    exact hnonreturn0 ⟨ψ L, hL.map (ResidueField.mapEquiv e).toRingHom, hψL, h⟩
  have hrest : MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField C →+* MvPolynomial (Fin 2) (ResidueField C))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' =
      MvPolynomial.map σ.toRingHom (MvPolynomial.eval₂Hom MvPolynomial.C
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q0) :=
    (map_firstZero σ.toRingHom q0).symm
  have hr'0 : MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField C →+* MvPolynomial (Fin 2) (ResidueField C))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' ≠ 0 := by
    rw [hrest]
    intro hz
    exact hr00 (MvPolynomial.map_injective σ.toRingHom σ.injective
      (hz.trans (map_zero (MvPolynomial.map σ.toRingHom)).symm))
  have hrns' : ¬ ∃ a : ResidueField C, a ≠ 0 ∧
      ∃ L : MvPolynomial (Fin 2) (ResidueField C), L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' =
          MvPolynomial.C a * L ^ 2 := by
    rw [hrest]
    exact fun h => hrns0 ((MvPolynomial.exists_scalar_homogeneous_square_map_iff
      σ.toRingHom σ.bijective _ 1).mp h)
  have hns' := MvPolynomial.not_scalar_homogeneous_square_of_first_zero_restriction q' hr'0 hrns'
  have hQ'0 : MvPolynomial.FirstCoordinate.dehom q' ≠ 0 := by
    intro hz
    apply hq'0
    apply MvPolynomial.FirstCoordinate.dehom_injective_on_homogeneous_two hq'
      (MvPolynomial.isHomogeneous_zero (Fin 3) (ResidueField C) 2)
    simpa only [map_zero] using hz
  have hdeg' : (MvPolynomial.FirstCoordinate.dehom q').totalDegree ≤ 2 := by
    rw [GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hq']
    exact GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree _
  have hcase' : ¬ ∃ a : ResidueField C, a ≠ 0 ∧ ∃ l : CaseOne.Plane C,
      l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q' =
        MvPolynomial.C a * l ^ 2 :=
    fun h => hns' ((MvPolynomial.FirstCoordinate.scalar_linear_square_iff hq' hq'0).mp h)
  exact ⟨p, g', q', hp, hgen', hmin, hcenter, hres, hq'0, hq', hker', hnonreturn,
    hr'0, hrns', hQ'0, hdeg', hcase', ⟨CaseOne.presentationOfKernel p g' hgen' q' hker'⟩⟩

end AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalCaseOneStep
