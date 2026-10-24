/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional.Powers
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ConnectedFibres
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.RegularQuotient
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Aglib.RingTheory.LocalRing.ParameterIdeal
public import Aglib.RingTheory.RegularLocalRing.FiniteNormalAlgebra
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Geometry of the full exceptional fibre of a rational surface blowup

The original finite ideal row gives a closed projective embedding of the full
exceptional scheme over its original residue field. Its positive twist is the
original restricted Cartier ideal. The original degree-zero and degree-one
section equivalences imply connectedness and exclude isolated closed points.
The actual Cartier stalk quotient then has ambient dimension two and supplies
a regular maximal-primary parameter on the exceptional stalk itself.

No reduction, coefficient-field section, Gorenstein assumption or Hilbert
function is used. Both regular and singular rational local surfaces are included.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

section ProjectiveEmbedding

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The original ordinary projective triangle restricted along the full exceptional fibre. -/
theorem exceptionalTautologicalEmbedding_base (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    (exceptionalCurveInclusion A hd ≫ tautologicalEmbedding A hd g hg) ≫
        ProjectiveSpace.toSpec A ι =
      exceptionalStructureMap A hd ≫ residueSpectrumInclusion A := by
  rw [Category.assoc, tautologicalEmbedding_toSpec]
  exact (exceptionalStructureMap_triangle A hd).symm

/-- The original finite-row projective embedding restricted to the full closed fibre,
through the actual coefficient base-change square. -/
def exceptionalTautologicalEmbedding (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    exceptionalCurve A hd ⟶ ProjectiveSpace (A ⧸ IsLocalRing.maximalIdeal A) ι :=
  (ProjectiveSpace.isPullback_map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) ι).lift
    (exceptionalCurveInclusion A hd ≫ tautologicalEmbedding A hd g hg)
    (exceptionalStructureMap A hd) (exceptionalTautologicalEmbedding_base A hd g hg)

/-- The coefficient projection is the original exceptional inclusion followed by
the original ordinary projective embedding. -/
theorem exceptionalTautologicalEmbedding_comp (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    exceptionalTautologicalEmbedding A hd g hg ≫
        ProjectiveSpace.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) ι =
      exceptionalCurveInclusion A hd ≫ tautologicalEmbedding A hd g hg :=
  (ProjectiveSpace.isPullback_map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) ι).lift_fst
    _ _ (exceptionalTautologicalEmbedding_base A hd g hg)

/-- The projective structural triangle uses the original residue-field map of E. -/
theorem exceptionalTautologicalEmbedding_toSpec (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    exceptionalTautologicalEmbedding A hd g hg ≫
        ProjectiveSpace.toSpec (A ⧸ IsLocalRing.maximalIdeal A) ι =
      exceptionalStructureMap A hd :=
  (ProjectiveSpace.isPullback_map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) ι).lift_snd
    _ _ (exceptionalTautologicalEmbedding_base A hd g hg)

/-- The same base-changed finite-row map is a closed immersion. -/
theorem exceptionalTautologicalEmbedding_isClosedImmersion (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    IsClosedImmersion (exceptionalTautologicalEmbedding A hd g hg) := by
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  let p := ProjectiveSpace.map q ι
  let : IsClosedImmersion (tautologicalEmbedding A hd g hg) :=
    tautologicalEmbedding_isClosedImmersion A hd g hg
  let : IsSeparated (Spec.map (CommRingCat.ofHom q)) := inferInstance
  let : IsSeparated p := MorphismProperty.of_isPullback
    (ProjectiveSpace.isPullback_map q ι).flip inferInstance
  let : IsClosedImmersion (exceptionalTautologicalEmbedding A hd g hg ≫ p) := by
    rw [show p = ProjectiveSpace.map q ι from rfl,
      exceptionalTautologicalEmbedding_comp]
    infer_instance
  exact IsClosedImmersion.of_comp (exceptionalTautologicalEmbedding A hd g hg) p

/-- The positive projective twist is the same original restricted ideal line.
Both comparisons come from the actual coefficient map and ordinary finite row. -/
def exceptionalTautologicalEmbeddingTwistingIso (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    (Modules.pullback (exceptionalTautologicalEmbedding A hd g hg)).obj
        (ProjectiveSpace.twistingSheaf (A ⧸ IsLocalRing.maximalIdeal A) ι 1) ≅
      (exceptionalLine A hd).val := by
  let i := exceptionalCurveInclusion A hd
  let j := tautologicalEmbedding A hd g hg
  let e := exceptionalTautologicalEmbedding A hd g hg
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  let p := ProjectiveSpace.map q ι
  let O := ProjectiveSpace.twistingSheaf A ι 1
  exact ((Modules.pullback e).mapIso (ProjectiveSpace.twistingPullbackIso q ι 1)).symm ≪≫
    (pullbackComp e p).app O ≪≫
      (pullbackCongr (exceptionalTautologicalEmbedding_comp A hd g hg)).app O ≪≫
        (pullbackComp i j).symm.app O ≪≫
          (Modules.pullback i).mapIso (tautologicalEmbeddingTwistingIso A hd g hg)

/-- Two zero entries pad the actual finite generators without changing their span.
The resulting matched projective embedding has ambient dimension at least one. -/
theorem exists_exceptionalTautologicalEmbedding (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] :
    ∃ (d : ℕ) (j : exceptionalCurve A hd ⟶
        ProjectiveSpace (A ⧸ IsLocalRing.maximalIdeal A) (ULift.{u} (Fin (d + 1)))),
      1 ≤ d ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace.toSpec (A ⧸ IsLocalRing.maximalIdeal A)
          (ULift.{u} (Fin (d + 1))) = exceptionalStructureMap A hd ∧
        Nonempty ((Modules.pullback j).obj
          (ProjectiveSpace.twistingSheaf (A ⧸ IsLocalRing.maximalIdeal A)
            (ULift.{u} (Fin (d + 1))) 1) ≅ (exceptionalLine A hd).val) := by
  obtain ⟨d, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := IsLocalRing.maximalIdeal A)
  let g' : ULift.{u} (Fin (d + 1 + 1)) → IsLocalRing.maximalIdeal A :=
    fun i => Fin.cases 0 (Fin.cases 0 g) i.down
  have hg' : Submodule.span A (Set.range g') = ⊤ := by
    apply top_unique
    rw [← hg]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨ULift.up i.succ.succ, rfl⟩
  exact ⟨d + 1, exceptionalTautologicalEmbedding A hd g' hg', Nat.le_add_left 1 d,
    exceptionalTautologicalEmbedding_isClosedImmersion A hd g' hg',
    exceptionalTautologicalEmbedding_toSpec A hd g' hg',
    ⟨exceptionalTautologicalEmbeddingTwistingIso A hd g' hg'⟩⟩

end ProjectiveEmbedding

section Topology

private theorem isOpen_singleton_of_closed_stalk_dimension_zero
    (X : Scheme.{u}) [NoetherianSpace X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hd : ringKrullDim (X.presheaf.stalk x) = 0) :
    IsOpen ({x} : Set X) := by
  classical
  have hzero : Order.coheight x = 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hd
    exact WithBot.coe_injective hd
  have hgen (y : X) (hy : y ⤳ x) : y = x :=
    (Specializes.antisymm hy ((Order.coheight_eq_zero.mp hzero) hy)).eq
  let S : Set (Set X) := {Z ∈ irreducibleComponents X | Z ≠ {x}}
  have hS : S.Finite := NoetherianSpace.finite_irreducibleComponents.subset
    (fun _ h => h.1)
  have hc : IsClosed (⋃ Z ∈ S, Z) := hS.isClosed_biUnion
    (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
  have he : ({x} : Set X) = (⋃ Z ∈ S, Z)ᶜ := by
    ext y
    constructor
    · intro hyx hy
      have hyx : y = x := hyx
      subst y
      obtain ⟨Z, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hZ, hxZ⟩ := Set.mem_iUnion.mp hy
      obtain ⟨z, hz⟩ := QuasiSober.sober hZ.1.1
        (isClosed_of_mem_irreducibleComponents Z hZ.1)
      have hzx : z = x := hgen z (hz.specializes hxZ)
      exact hZ.2 (hz.symm.trans
        ((congrArg (fun z : X => closure ({z} : Set X)) hzx).trans hx.closure_eq))
    · intro hy
      by_contra hne
      have hZ : irreducibleComponent y ∈ S := by
        refine ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
        intro heq
        exact hne (heq ▸ (mem_irreducibleComponent : y ∈ irreducibleComponent y))
      exact hy (Set.mem_iUnion.mpr ⟨irreducibleComponent y,
        Set.mem_iUnion.mpr ⟨hZ, mem_irreducibleComponent⟩⟩)
  rw [he]
  exact hc.isOpen_compl

end Topology

section CartierStalk

private theorem cartierStalk_regularGenerator {E X : Scheme.{u}}
    (i : E ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (x : E) :
    ∃ t : X.presheaf.stalk (i x), t ∈ IsLocalRing.maximalIdeal _ ∧
      IsSMulRegular (X.presheaf.stalk (i x)) t ∧
      RingHom.ker (i.stalkMap x).hom = Ideal.span {t} := by
  let R := X.presheaf.stalk (i x)
  let L : LineBundle (Spec R) :=
    ⟨(Modules.pullback (X.fromSpecStalk (i x))).obj (idealModule i),
      pullback_locallyRankOne _ _ hI⟩
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing R L
  let eM : (moduleStalk X (i x)).obj (idealModule i) ≅ ModuleCat.of R R :=
    stalkFromSpecStalkSectionsIso X (i x) (idealModule i) ≪≫
      moduleSpecΓFunctor.mapIso e ≪≫ (tilde.isoTop (ModuleCat.of R R)).symm
  let eK : RingHom.ker (i.stalkMap x).hom ≃ₗ[R] R :=
    (LinearEquiv.ofEq _ _ (i.ker_stalkIdeal_eq_ker_stalkMap x).symm).trans
      ((idealModuleStalkEquiv i (i x)).symm.trans eM.toLinearEquiv)
  obtain ⟨t, ht, hker⟩ := Ideal.ideal_exists_regular_generator
    (RingHom.ker (i.stalkMap x).hom) eK
  have htker : t ∈ RingHom.ker (i.stalkMap x).hom := by
    rw [hker]
    exact Ideal.mem_span_singleton_self t
  exact ⟨t, IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) htker, ht, hker⟩

private theorem regularParameter_of_principal_surjection
    {R B : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing B] [IsLocalRing B]
    (φ : R →+* B) (hφ : Function.Surjective φ)
    (hdim : ringKrullDim R = 2) (t : R) (ht0 : t ≠ 0)
    (ht : t ∈ IsLocalRing.maximalIdeal R)
    (hker : RingHom.ker φ = Ideal.span {t}) :
    ∃ s ∈ IsLocalRing.maximalIdeal R,
      φ s ∈ IsLocalRing.maximalIdeal B ∧ IsSMulRegular B (φ s) ∧
      (Ideal.span {φ s}).radical = IsLocalRing.maximalIdeal B := by
  let : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  let : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  obtain ⟨s, hs, hrad⟩ := IsLocalRing.exists_parameter_pair_containing R t ht0 ht
  have havoid : ∀ P : Ideal R, P.IsPrime → P.height = 1 → t ∈ P → s ∉ P := by
    intro P hP hheight htP hsP
    let : P.IsPrime := hP
    have hle : Ideal.span {t} ⊔ Ideal.span {s} ≤ P :=
      sup_le (P.span_singleton_le_iff_mem.mpr htP)
        (P.span_singleton_le_iff_mem.mpr hsP)
    have hmle : IsLocalRing.maximalIdeal R ≤ P := by
      rw [← hrad]
      exact hP.radical_le_iff.mpr hle
    have he : IsLocalRing.maximalIdeal R = P :=
      le_antisymm hmle (IsLocalRing.le_maximalIdeal_of_isPrime P)
    have hd : 2 ≤ ringKrullDim R := hdim.ge
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, he, hheight] at hd
    norm_num at hd
  let Q := R ⧸ Ideal.span {t}
  let q : R →+* Q := Ideal.Quotient.mk (Ideal.span {t})
  have hreg : IsSMulRegular Q s :=
    IsIntegrallyClosed.isSMulRegular_quotient_of_pair_avoids_height_one t s ht0 havoid
  let e : Q ≃+* B := (Ideal.quotEquivOfEq hker.symm).trans
    (φ.quotientKerEquivOfSurjective hφ)
  have he (a : R) : e (q a) = φ a := by
    have hq : (Ideal.quotEquivOfEq hker.symm) (q a) =
        Ideal.Quotient.mk (RingHom.ker φ) a := rfl
    exact (congrArg (φ.quotientKerEquivOfSurjective hφ) hq).trans
      (show φ.quotientKerEquivOfSurjective hφ
        (Ideal.Quotient.mk (RingHom.ker φ) a) = φ a from rfl)
  refine ⟨s, hs, map_nonunit φ s hs, ?_, ?_⟩
  · intro x y hxy
    apply e.symm.injective
    apply hreg
    apply e.injective
    change e (q s * e.symm x) = e (q s * e.symm y)
    simpa only [map_mul, he, e.apply_symm_apply, smul_eq_mul] using hxy
  · have hkerle : RingHom.ker φ ≤ Ideal.span {t} ⊔ Ideal.span {s} := by
      rw [hker]
      exact le_sup_left
    have h := congrArg (Ideal.map φ) hrad
    rw [Ideal.map_radical_of_surjective hφ hkerle,
      IsLocalRing.map_maximalIdeal_of_surjective φ hφ] at h
    have htker : t ∈ RingHom.ker φ := by
      rw [hker]
      exact Ideal.mem_span_singleton_self t
    have hφt : φ t = 0 := htker
    simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hφt,
      Ideal.span_singleton_zero, bot_sup_eq] using h

end CartierStalk

section ResidueSections

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The native first power layer is the actual cotangent space, over the original residue field. -/
def exceptionalPowerOneCotangentEquiv :
    exceptionalPowerLayer A 1 ≃ₗ[A ⧸ IsLocalRing.maximalIdeal A]
      IsLocalRing.CotangentSpace A := by
  let m := IsLocalRing.maximalIdeal A
  let e (J : Ideal A) (hJ : J = m) :
      (J ⧸ (m • (⊤ : Submodule A J))) ≃ₗ[A ⧸ m] IsLocalRing.CotangentSpace A := by
    subst J
    exact LinearEquiv.refl (A ⧸ m) (IsLocalRing.CotangentSpace A)
  exact e (m ^ 1) (pow_one m)

/-- The actual first power layer has dimension at least two by the local generator bound. -/
theorem exceptionalPowerLayer_one_finrank_ge_two (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] :
    2 ≤ Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (exceptionalPowerLayer A 1) := by
  have hfr : (IsLocalRing.maximalIdeal A).spanFinrank =
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (exceptionalPowerLayer A 1) := by
    have hcot : (IsLocalRing.maximalIdeal A).spanFinrank =
        Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (IsLocalRing.CotangentSpace A) :=
      IsLocalRing.spanFinrank_eq_finrank_quotient (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
    exact hcot.trans (exceptionalPowerOneCotangentEquiv A).finrank_eq.symm
  have h := ringKrullDim_le_spanFinrank_maximalIdeal A
  rw [hd, hfr] at h
  exact_mod_cast h

/-- The original full exceptional fibre is Noetherian. -/
theorem exceptionalCurve_isNoetherian (hd : ringKrullDim A = 2) [IsNoetherianRing A] :
    IsNoetherian (exceptionalCurve A hd) := by
  let p := exceptionalStructureMap A hd
  let : IsProper p := exceptionalStructureMap_isProper A hd
  let : IsLocallyNoetherian (exceptionalCurve A hd) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace (exceptionalCurve A hd) := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

omit [IsIntegrallyClosed A] in
/-- Surjectivity of the actual closed fibre gives a point of the full exceptional scheme. -/
theorem exceptionalCurve_nonempty (hd : ringKrullDim A = 2) :
    Nonempty (exceptionalCurve A hd) := by
  let : Surjective (exceptionalStructureMap A hd) := exceptionalStructureMap_surjective A hd
  obtain ⟨x, _⟩ := (exceptionalStructureMap A hd).surjective
    (genericPoint (Spec (.of (A ⧸ IsLocalRing.maximalIdeal A))))
  exact ⟨x⟩

/-- Connectedness follows from the ORIGINAL residue-field coefficient isomorphism. -/
theorem exceptionalCurve_connectedSpace (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    ConnectedSpace (exceptionalCurve A hd) := by
  let : Nonempty (exceptionalCurve A hd) := exceptionalCurve_nonempty A hd
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let e := exceptionalCoefficientsEquiv A hd hA hRat
  apply Scheme.connectedSpace_of_globalSections_idempotents (exceptionalCurve A hd)
  intro a ha
  have hi : IsIdempotentElem (e.symm a) := by
    change e.symm a * e.symm a = e.symm a
    rw [← map_mul, ha]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hi with h | h
  · left
    apply e.symm.injective
    exact h.trans (map_zero e.symm).symm
  · right
    apply e.symm.injective
    exact h.trans (map_one e.symm).symm

/-- A singleton full fibre would make its actual degree-one line trivial and
contradict the dimension of the original cotangent space. -/
theorem exceptionalCurve_not_subsingleton (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    ¬ Subsingleton (exceptionalCurve A hd) := by
  intro hsub
  let : Subsingleton (exceptionalCurve A hd) := hsub
  let E := exceptionalCurve A hd
  let κ := A ⧸ IsLocalRing.maximalIdeal A
  let : Field κ := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  let c : κ →+* Γ(E, ⊤) := exceptionalCoefficients A hd
  let F := Cohomology.moduleGlobalSectionsFunctorOfHom E c
  let L : LineBundle E := ⟨exceptionalPower A hd 1,
    pullback_locallyRankOne _ _ (ordinaryIdealPower_locallyRankOne A hd 1)⟩
  obtain ⟨x⟩ := exceptionalCurve_nonempty A hd
  obtain ⟨e⟩ := nonempty_iso_unit_of_forall_mem_open x (fun U hx => by
    apply top_unique
    intro y _
    exact Subsingleton.elim x y ▸ hx) L
  let eS : exceptionalPowerSections A hd 1 ≃ₗ[κ] F.obj (originalUnit E) :=
    (F.mapIso e).toLinearEquiv
  let N : ModuleCat.{u} κ := F.obj (originalUnit E)
  let cL : κ →ₗ[κ] N :=
    { toFun := fun a => (show N from c a)
      map_add' := fun a b => c.map_add a b
      map_smul' := fun a b => by
        change c (a * b) = c a * c b
        exact c.map_mul a b }
  let eC : κ ≃ₗ[κ] N := LinearEquiv.ofBijective cL
    (exceptionalCoefficients_bijective A hd hA hRat)
  have hdim : Module.finrank κ (exceptionalPowerLayer A 1) = 1 :=
    (((exceptionalPowerTheta A hd hA hRat 1).trans eS).trans eC.symm).finrank_eq.trans
      (Module.finrank_self κ)
  have htwo := exceptionalPowerLayer_one_finrank_ge_two A hd
  rw [hdim] at htwo
  omega

/-- No closed point of the original full exceptional curve is isolated. -/
theorem exceptionalCurve_closedPoint_not_isOpen (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (x : exceptionalCurve A hd) (hx : IsClosed ({x} : Set (exceptionalCurve A hd))) :
    ¬ IsOpen ({x} : Set (exceptionalCurve A hd)) := by
  intro hxo
  let : ConnectedSpace (exceptionalCurve A hd) := exceptionalCurve_connectedSpace A hd hA hRat
  have he : ({x} : Set (exceptionalCurve A hd)) = Set.univ :=
    (show IsClopen ({x} : Set (exceptionalCurve A hd)) from ⟨hx, hxo⟩).eq_univ
      (Set.singleton_nonempty x)
  apply exceptionalCurve_not_subsingleton A hd hA hRat
  refine ⟨fun y z => ?_⟩
  have hy : y = x := by
    have hy : y ∈ ({x} : Set (exceptionalCurve A hd)) := by rw [he]; trivial
    exact hy
  have hz : z = x := by
    have hz : z ∈ ({x} : Set (exceptionalCurve A hd)) := by rw [he]; trivial
    exact hz
  exact hy.trans hz.symm

end ResidueSections

section StalkGeometry

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- The actual ordinary source has dimension at most two, transported through
the original normalization isomorphism from its proved chart dimension bound. -/
theorem ordinary_dimension_le_two (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    topologicalKrullDim (source A hd) ≤ 2 := by
  let : IsIso (nu A hd) := normalization_isIso A hd hA hRat
  have he := IsHomeomorph.topologicalKrullDim_eq (nu A hd)
    (asIso (nu A hd)).hom.homeomorph.isHomeomorph
  exact he.symm.le.trans (normalization_dimension_le_two A hd hA)

/-- Every closed point of the FULL exceptional fibre has ambient local dimension two.
The argument uses the original theta0/theta1 maps, not a closed-point dimension axiom. -/
theorem exceptionalCurve_closedPoint_stalk_dimension (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (x : exceptionalCurve A hd) (hx : IsClosed ({x} : Set (exceptionalCurve A hd))) :
    ringKrullDim ((source A hd).presheaf.stalk (exceptionalCurveInclusion A hd x)) = 2 := by
  let X := source A hd
  let E := exceptionalCurve A hd
  let i := exceptionalCurveInclusion A hd
  let R := X.presheaf.stalk (i x)
  let B := E.presheaf.stalk x
  have hle : ringKrullDim R ≤ 2 :=
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) (i x)).trans
      ((Scheme.topologicalKrullDim_eq_iSup_stalk X).symm.le.trans
        (ordinary_dimension_le_two A hd hA hRat))
  apply le_antisymm hle
  by_contra hnot
  have hsmall : ringKrullDim R ≤ 1 :=
    ENat.WithBot.lt_add_one_iff.mp (by norm_num; exact lt_of_not_ge hnot)
  obtain ⟨t, _, htreg, hker⟩ := cartierStalk_regularGenerator i (datum A).cartier x
  have ht0 : t ≠ 0 := by
    intro ht
    have h01 : (0 : R) = 1 := htreg (by simp [ht])
    exact zero_ne_one h01
  have htker : t ∈ RingHom.ker (i.stalkMap x).hom := by
    rw [hker]
    exact Ideal.mem_span_singleton_self t
  have hquot : ringKrullDim B + 1 ≤ ringKrullDim R :=
    ringKrullDim_succ_le_of_surjective (i.stalkMap x).hom (i.stalkMap_surjective x)
      (mem_nonZeroDivisors_of_ne_zero ht0) htker
  have hsucc : (Order.coheight x : WithBot ℕ∞) + 1 ≤ 1 := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact hquot.trans hsmall
  have hc : Order.coheight x + 1 ≤ (1 : ℕ∞) :=
    WithBot.coe_le_coe.mp (by simpa only [WithBot.coe_add, WithBot.coe_one] using hsucc)
  have hz : Order.coheight x = 0 := le_antisymm
    ((ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (by simpa using hc))
    (show (0 : ℕ∞) ≤ Order.coheight x from bot_le)
  have hdim : ringKrullDim B = 0 := by
    change ringKrullDim (E.presheaf.stalk x) = 0
    rw [ringKrullDim_stalk_eq_coheight, hz]
    rfl
  let : IsNoetherian E := exceptionalCurve_isNoetherian A hd
  exact exceptionalCurve_closedPoint_not_isOpen A hd hA hRat x hx
    (isOpen_singleton_of_closed_stalk_dimension_zero E x hx hdim)

/-- The actual exceptional stalk has a regular parameter whose radical is its
maximal ideal; the element is the image of a parameter in the actual ambient stalk. -/
theorem exceptionalCurve_closedPoint_regularParameter (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (x : exceptionalCurve A hd) (hx : IsClosed ({x} : Set (exceptionalCurve A hd))) :
    ∃ s ∈ IsLocalRing.maximalIdeal
        ((source A hd).presheaf.stalk (exceptionalCurveInclusion A hd x)),
      (exceptionalCurveInclusion A hd).stalkMap x s ∈
        IsLocalRing.maximalIdeal ((exceptionalCurve A hd).presheaf.stalk x) ∧
      IsSMulRegular ((exceptionalCurve A hd).presheaf.stalk x)
        ((exceptionalCurveInclusion A hd).stalkMap x s) ∧
      (Ideal.span {(exceptionalCurveInclusion A hd).stalkMap x s}).radical =
        IsLocalRing.maximalIdeal ((exceptionalCurve A hd).presheaf.stalk x) := by
  let X := source A hd
  let i := exceptionalCurveInclusion A hd
  let R := X.presheaf.stalk (i x)
  let : IsIntegrallyClosed R := (ordinary_normalStalks A hd hA hRat (i x)).2
  obtain ⟨t, ht, htreg, hker⟩ := cartierStalk_regularGenerator i (datum A).cartier x
  have ht0 : t ≠ 0 := by
    intro ht
    have h01 : (0 : R) = 1 := htreg (by simp [ht])
    exact zero_ne_one h01
  exact regularParameter_of_principal_surjection (i.stalkMap x).hom
    (i.stalkMap_surjective x) (exceptionalCurve_closedPoint_stalk_dimension A hd hA hRat x hx)
    t ht0 ht hker

/-- The regular-primary closed-stalk input for the actual nonreduced CM-curve consumer. -/
theorem exceptionalCurve_closedPoint_cmParameter (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (x : exceptionalCurve A hd) (hx : IsClosed ({x} : Set (exceptionalCurve A hd))) :
    ∃ b ∈ IsLocalRing.maximalIdeal ((exceptionalCurve A hd).presheaf.stalk x),
      IsSMulRegular ((exceptionalCurve A hd).presheaf.stalk x) b ∧
      (Ideal.span {b}).radical =
        IsLocalRing.maximalIdeal ((exceptionalCurve A hd).presheaf.stalk x) := by
  obtain ⟨s, _, hs, hreg, hrad⟩ :=
    exceptionalCurve_closedPoint_regularParameter A hd hA hRat x hx
  exact ⟨(exceptionalCurveInclusion A hd).stalkMap x s, hs, hreg, hrad⟩

end StalkGeometry

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

