/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CompactSupportTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FinitePushforward
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LevelMaps
public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FibreDegree
public import Aglib.AlgebraicGeometry.FunctionField.OpenSquare
public import Aglib.RingTheory.ZMod.Reduction

/-!
# Original normalized trace under level reduction and curve pullback

Canonical roots powers reduce the Aglib-normalized trace by the canonical
ZMod quotient map. Pullback of an actual finite dominant curve map of constant
locally free rank multiplies trace by that rank, through the original Picard
pullback and its proved degree formula. No norm on Picard groups, purity,
primitive-root compatibility or SGA sign comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

namespace CompactSupport

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(X, ⊤)))

/-- The entire original roots counit commutes with the canonical coefficient level map. -/
theorem rootsExtensionMap_level :
    (etaleLowerShriek j).map (rootsLevelMap U m n) ≫ rootsExtensionMap j n hn hinv =
      rootsExtensionMap j (m * n) (Nat.mul_pos hm hn) hinv' ≫ rootsLevelMap X m n := by
  have h := rootsLevelMap_pullback_inv j m n hm hn hinv hinv'
  change (etaleLowerShriek j).map (rootsLevelMap U m n) ≫
      ((etaleLowerShriek j).map (rootsPullbackIso j n hn hinv).inv ≫
        (etaleLowerShriekAdjunction j).counit.app (mu X n)) = _
  rw [← Category.assoc, ← (etaleLowerShriek j).map_comp, h,
    (etaleLowerShriek j).map_comp]
  have hc := (etaleLowerShriekAdjunction j).counit.naturality (rootsLevelMap X m n)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hc
  change _ = ((etaleLowerShriek j).map
      (rootsPullbackIso j (m * n) (Nat.mul_pos hm hn) hinv').inv ≫
        (etaleLowerShriekAdjunction j).counit.app (mu X (m * n))) ≫ rootsLevelMap X m n
  simp only [Category.assoc]
  rw [hc]

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The whole original compact-to-ordinary cohomology map preserves roots level reduction. -/
theorem rootsMap_level (q : ℕ) :
    (rootsMap j n hn hinv q).comp (H.map j (rootsLevelMap U m n) q) =
      (Sheaf.H.map (rootsLevelMap X m n) q).comp
        (rootsMap j (m * n) (Nat.mul_pos hm hn) hinv' q) := by
  apply AddMonoidHom.ext
  intro c
  change Sheaf.H.map (rootsExtensionMap j n hn hinv) q
      (Sheaf.H.map ((etaleLowerShriek j).map (rootsLevelMap U m n)) q c) =
    Sheaf.H.map (rootsLevelMap X m n) q
      (Sheaf.H.map (rootsExtensionMap j (m * n) (Nat.mul_pos hm hn) hinv') q c)
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    rootsExtensionMap_level j m n hm hn hinv hinv']

end CompactSupport

namespace CompactSupport

variable {V U Y X : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
  (f : V ⟶ U) (jU : U ⟶ X) [IsOpenImmersion jU]
  (jV : V ⟶ Y) [IsOpenImmersion jV] (h : IsPullback jV f p jU)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]

/-- The whole original compact roots pullback commutes with passage to ordinary
cohomology on the given finite Cartesian completions. Ramification is allowed. -/
theorem rootsMap_finiteRootsPullback (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    (rootsMap jV n hn (levelInvertible p n hinv) q).comp
        (finiteRootsPullbackMap p f jU jV h n q) =
      (Kummer.rootsCohomologyPullback p n hn hinv q).comp (rootsMap jU n hn hinv q) := by
  have hs : (etaleLowerShriek jU).map (rootsUnit f n) ≫
      (finiteLowerShriekDirectImageMap p f jU jV h).app (mu V n) ≫
      (directImage p).map (rootsExtensionMap jV n hn (levelInvertible p n hinv)) =
    rootsExtensionMap jU n hn hinv ≫ rootsUnit p n :=
    finiteLowerShriekDirectImageMap_roots_unit p f jU jV h n hn hinv
  apply AddMonoidHom.ext
  intro x
  change Sheaf.H.map (rootsExtensionMap jV n hn (levelInvertible p n hinv)) q
      (Finite.finiteCohomologyDirectImageAddEquiv p ((etaleLowerShriek jV).obj (mu V n)) q
        (Sheaf.H.map ((finiteLowerShriekDirectImageMap p f jU jV h).app (mu V n)) q
          (Sheaf.H.map ((etaleLowerShriek jU).map (rootsUnit f n)) q x))) =
    Sheaf.H.map (rootsPullbackIso p n hn hinv).hom q
      (cohomologyPullback p (mu X n) q (Sheaf.H.map (rootsExtensionMap jU n hn hinv) q x))
  rw [← Finite.finiteCohomologyDirectImageAddEquiv_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, hs, Sheaf.H.map_comp_apply,
    ← rootsPullbackIso_unit p n hn hinv, Sheaf.H.map_comp_apply,
    Finite.finiteCohomologyDirectImageAddEquiv_naturality]
  exact congrArg (Sheaf.H.map (rootsPullbackIso p n hn hinv).hom q)
    (cohomologyDirectImageAddEquiv_unit p (mu X n) q
      (Sheaf.H.map (rootsExtensionMap jU n hn hinv) q x))

end CompactSupport

private theorem trace_eq_of_raised_level
    {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (eA : A ≃+ ZMod n) (eB : B ≃+ ZMod n)
    (eA' : A' ≃+ ZMod (n ^ d * n)) (eB' : B' ≃+ ZMod (n ^ d * n))
    (T : B →+ A) (T' : B' →+ A') (P' : A' →+ B')
    (rA : A' →+ A) (rB : B' →+ B)
    (hP : ∀ a, eB' (P' a) = d • eA' a)
    (hTP : ∀ a, T' (P' a) = d • a)
    (hA : ∀ a, eA (rA a) = ZMod.castHom (dvd_mul_left n (n ^ d)) (ZMod n) (eA' a))
    (hB : ∀ b, eB (rB b) = ZMod.castHom (dvd_mul_left n (n ^ d)) (ZMod n) (eB' b))
    (hT : ∀ b, T (rB b) = rA (T' b)) :
    eA.toAddMonoidHom.comp T = eB.toAddMonoidHom := by
  let a := eA'.symm 1
  let b := eB'.symm 1
  have hp : P' a = d • b := by
    apply eB'.injective
    rw [hP, map_nsmul]
    simp only [a, b, AddEquiv.apply_symm_apply]
  have hs : d • eA' (T' b) = d • (1 : ZMod (n ^ d * n)) := by
    calc
      d • eA' (T' b) = eA' (T' (d • b)) := by simp only [map_nsmul]
      _ = eA' (T' (P' a)) := congrArg (fun z => eA' (T' z)) hp.symm
      _ = d • (1 : ZMod (n ^ d * n)) := by
        rw [hTP, map_nsmul]
        exact congrArg (fun z => d • z) (eA'.apply_symm_apply 1)
  have hz : d • (eA' (T' b) - 1) = 0 := by rw [nsmul_sub, hs, sub_self]
  have hred : ZMod.castHom (dvd_mul_left n (n ^ d)) (ZMod n) (eA' (T' b)) = 1 := by
    have hz' : ZMod.castHom (dvd_mul_left n (n ^ d)) (ZMod n) (eA' (T' b) - 1) = 0 := by
      have hkill (N : ℕ) (hN : N = n ^ (d + 1)) (hdiv : n ∣ N)
          (x : ZMod N) (hx : d • x = 0) : ZMod.castHom hdiv (ZMod n) x = 0 := by
        subst N
        exact ZMod.castHom_eq_zero_of_nsmul_eq_zero_pow_succ hn hd x hx
      exact hkill (n ^ d * n) (pow_succ n d).symm (dvd_mul_left n (n ^ d))
        (eA' (T' b) - 1) hz
    simpa only [map_sub, map_one, sub_eq_zero] using hz'
  have hb : rB b = eB.symm 1 := by
    apply eB.injective
    rw [hB]
    simp only [b, AddEquiv.apply_symm_apply, map_one]
  have h1 : eA (T (eB.symm 1)) = 1 := by
    rw [← hb, hT, hA]
    exact hred
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply AddMonoidHom.ext
  intro x
  have hx : x = (eB x).val • eB.symm 1 := by
    apply eB.injective
    simp only [map_nsmul, AddEquiv.apply_symm_apply, nsmul_eq_mul, mul_one,
      ZMod.natCast_zmod_val]
  change eA (T x) = eB x
  rw [hx, map_nsmul, map_nsmul, h1, map_nsmul, AddEquiv.apply_symm_apply]

namespace Curves

open Scheme.OverField

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

include hX in
private theorem proper_picardBoundary_surjective (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Function.Surjective (Kummer.picardBoundary X.left n hn hinv) := by
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := hX.proper
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact picardBoundary_surjective_of_curve k X.left X.hom hX.topologicalKrullDim_eq_one.le
    n hn hunit hinv

/-- The whole normalized trace reduces by the canonical ZMod quotient under the original
roots power map, with no independently chosen primitive roots. -/
theorem traceAddEquiv_level (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hunit' : IsUnit ((m * n : ℕ) : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(X.left, ⊤))) :
    (traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
        (Sheaf.H.map (rootsLevelMap X.left m n) 2) =
      (ZMod.castHom (dvd_mul_left n m) (ZMod n)).toAddMonoidHom.comp
        (traceAddEquiv hX (m * n) (Nat.mul_pos hm hn) hunit' hinv').toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨a, rfl⟩ := proper_picardBoundary_surjective hX (m * n)
    (Nat.mul_pos hm hn) hunit' hinv' c
  change traceAddEquiv hX n hn hunit hinv
      (Sheaf.H.map (rootsLevelMap X.left m n) 2
        (Kummer.picardBoundary X.left (m * n) (Nat.mul_pos hm hn) hinv' a)) =
    ZMod.castHom (dvd_mul_left n m) (ZMod n)
      (traceAddEquiv hX (m * n) (Nat.mul_pos hm hn) hunit' hinv'
        (Kummer.picardBoundary X.left (m * n) (Nat.mul_pos hm hn) hinv' a))
  have hl := DFunLike.congr_fun
    (Kummer.picardBoundary_level X.left m n hm hn hinv hinv') a
  change Sheaf.H.map (rootsLevelMap X.left m n) 2
      (Kummer.picardBoundary X.left (m * n) (Nat.mul_pos hm hn) hinv' a) =
    Kummer.picardBoundary X.left n hn hinv a at hl
  rw [hl, traceAddEquiv_picardBoundary, traceAddEquiv_picardBoundary]
  exact (_root_.map_intCast (ZMod.castHom (dvd_mul_left n m) (ZMod n)) _).symm

/-- The same canonical reduction law holds for the original compact-support trace. -/
theorem compactSupportTraceAddEquiv_level
    (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hunit' : IsUnit ((m * n : ℕ) : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(X.left, ⊤))) :
    (compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv).toAddMonoidHom.comp
        (CompactSupport.H.map j (rootsLevelMap U m n) 2) =
      (ZMod.castHom (dvd_mul_left n m) (ZMod n)).toAddMonoidHom.comp
        (compactSupportTraceAddEquiv X hX D hfin hclosed j hD (m * n)
          (Nat.mul_pos hm hn) hunit' hinv').toAddMonoidHom := by
  change ((traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
      (CompactSupport.rootsMap j n hn hinv 2)).comp _ =
    (ZMod.castHom (dvd_mul_left n m) (ZMod n)).toAddMonoidHom.comp
      ((traceAddEquiv hX (m * n) (Nat.mul_pos hm hn) hunit' hinv').toAddMonoidHom.comp
        (CompactSupport.rootsMap j (m * n) (Nat.mul_pos hm hn) hinv' 2))
  rw [AddMonoidHom.comp_assoc, CompactSupport.rootsMap_level j m n hm hn hinv hinv' 2,
    ← AddMonoidHom.comp_assoc, traceAddEquiv_level hX m n hm hn hunit hunit' hinv hinv',
    AddMonoidHom.comp_assoc]

variable {Y : FScheme k} (hY : Curve.Properties Y)
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.left)]

/-- Proper trace scales by the actual function-field degree of the original
finite map. This intermediate form retains only finiteness of that field
extension; a dense finite-etale open supplies it below. -/
theorem traceAddEquiv_pullback_of_functionField_finite
    (p : Y ⟶ X) [IsFinite p.left] [IsDominant p.left]
    (hfin : letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
      letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
      letI := functionFieldMapAlgebra p.left
      Module.Finite X.left.functionField Y.left.functionField)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
    letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
    (traceAddEquiv hY n hn hunit (levelInvertible p.left n hinv)).toAddMonoidHom.comp
        (Kummer.rootsCohomologyPullback p.left n hn hinv 2) =
      Scheme.Hom.FiniteFlat.functionFieldDegree p.left •
        (traceAddEquiv hX n hn hunit hinv).toAddMonoidHom := by
  let := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  let := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
  let := Curve.curveProperties_isNoetherian hX
  let := Curve.curveProperties_isNoetherian hY
  let (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    Curve.curveProperties_closedPoint_stalk_dvr smoothFieldNormality smoothFieldRegularity
      smoothClosedPointDimension hX x.val x.property
  let (y : ClosedPoint Y.left) : IsDiscreteValuationRing (Y.left.presheaf.stalk y.val) :=
    Curve.curveProperties_closedPoint_stalk_dvr smoothFieldNormality smoothFieldRegularity
      smoothClosedPointDimension hY y.val y.property
  let := hX.proper
  let := hY.proper
  apply AddMonoidHom.ext
  intro c
  obtain ⟨a, rfl⟩ := proper_picardBoundary_surjective hX n hn hunit hinv c
  change traceAddEquiv hY n hn hunit (levelInvertible p.left n hinv)
      (Kummer.rootsCohomologyPullback p.left n hn hinv 2
        (Kummer.picardBoundary X.left n hn hinv a)) =
    Scheme.Hom.FiniteFlat.functionFieldDegree p.left •
      traceAddEquiv hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv a)
  rw [Kummer.picardBoundary_pullback, traceAddEquiv_picardBoundary,
    traceAddEquiv_picardBoundary]
  have hdegree := Curve.Picard.NormDegree.picardDegree_pullback p.left X.hom
    Curve.Picard.NormDegree.finiteMorphismNormOrder
    (le_of_eq (Curve.curveProperties_dimension smoothFieldDimension hY))
    (le_of_eq (Curve.curveProperties_dimension smoothFieldDimension hX)) hfin
    (Curve.Picard.Degree.properCurveProductFormula k Y.left (p.left ≫ X.hom)
      (Curve.curveProperties_dimension smoothFieldDimension hY))
    (Curve.Picard.Degree.properCurveProductFormula k X.left X.hom
      (Curve.curveProperties_dimension smoothFieldDimension hX)) a
  have hdegree' : Curve.curveDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Curve.Picard.Degree.properCurveProductFormula Y hY
        (Scheme.Modules.Invertible.pullbackClass p.left a) =
    (Scheme.Hom.FiniteFlat.functionFieldDegree p.left : ℤ) *
      Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX a := by
    simpa only [Curve.curveDegree, Over.w, Scheme.Hom.fieldDegree,
      Scheme.Hom.FiniteFlat.functionFieldDegree] using hdegree
  rw [hdegree', Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]

/-- The whole compact pullback scales the original trace by the completion's
actual function-field degree, without flatness of the completion map. -/
theorem compactSupportTraceAddEquiv_finitePullback_of_functionField_finite
    (p : Y ⟶ X) [IsFinite p.left] [IsDominant p.left]
    (hfin : letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
      letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
      letI := functionFieldMapAlgebra p.left
      Module.Finite X.left.functionField Y.left.functionField)
    (DX : Set X.left) (hfinX : DX.Finite)
    (hclosedX : ∀ x ∈ DX, IsClosed ({x} : Set X.left))
    (DY : Set Y.left) (hfinY : DY.Finite)
    (hclosedY : ∀ y ∈ DY, IsClosed ({y} : Set Y.left))
    {U V : Scheme.{u}} (jU : U ⟶ X.left) [IsOpenImmersion jU] (hDX : Set.range jU = DXᶜ)
    (jV : V ⟶ Y.left) [IsOpenImmersion jV] (hDY : Set.range jV = DYᶜ)
    (f : V ⟶ U) (hsq : IsPullback jV f p.left jU)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
    letI := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
    (compactSupportTraceAddEquiv Y hY DY hfinY hclosedY jV hDY n hn hunit
      (levelInvertible p.left n hinv)).toAddMonoidHom.comp
        (CompactSupport.finiteRootsPullbackMap p.left f jU jV hsq n 2) =
      Scheme.Hom.FiniteFlat.functionFieldDegree p.left •
        (compactSupportTraceAddEquiv X hX DX hfinX hclosedX jU hDX n hn hunit
          hinv).toAddMonoidHom := by
  let := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  let := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
  change ((traceAddEquiv hY n hn hunit (levelInvertible p.left n hinv)).toAddMonoidHom.comp
      (CompactSupport.rootsMap jV n hn (levelInvertible p.left n hinv) 2)).comp _ =
    Scheme.Hom.FiniteFlat.functionFieldDegree p.left •
      ((traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
        (CompactSupport.rootsMap jU n hn hinv 2))
  rw [AddMonoidHom.comp_assoc,
    CompactSupport.rootsMap_finiteRootsPullback p.left f jU jV hsq n hn hinv 2,
    ← AddMonoidHom.comp_assoc,
    traceAddEquiv_pullback_of_functionField_finite hX hY p hfin n hn hunit hinv]
  apply AddMonoidHom.ext
  intro x
  rfl

/-- The actual normalized proper trace scales by the original finite locally free rank
under the original geometric roots pullback. Ramification is allowed. -/
theorem traceAddEquiv_pullback_of_hasLocallyFreeRank
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (d : ℕ) (hd : Scheme.Hom.HasLocallyFreeRank f.left d)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    (traceAddEquiv hY n hn hunit (levelInvertible f.left n hinv)).toAddMonoidHom.comp
        (Kummer.rootsCohomologyPullback f.left n hn hinv 2) =
      d • (traceAddEquiv hX n hn hunit hinv).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨a, rfl⟩ := proper_picardBoundary_surjective hX n hn hunit hinv c
  change traceAddEquiv hY n hn hunit (levelInvertible f.left n hinv)
      (Kummer.rootsCohomologyPullback f.left n hn hinv 2
        (Kummer.picardBoundary X.left n hn hinv a)) =
    d • traceAddEquiv hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv a)
  rw [Kummer.picardBoundary_pullback, traceAddEquiv_picardBoundary,
    traceAddEquiv_picardBoundary]
  have hdegree := Curve.curveDegree_pullback_of_hasLocallyFreeRank
    smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Curve.Picard.Degree.properCurveProductFormula
    Scheme.Modules.affineModuleBaseChange Scheme.Hom.FiniteFlat.finiteDominantGenericFibre
    Curve.Picard.NormDegree.finiteMorphismNormOrder f hY hX d hd a
  rw [hdegree, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]

/-- The actual compact roots pullback scales normalized trace by the actual
finite locally free completion rank. Both finite complements may be empty. -/
theorem compactSupportTraceAddEquiv_finitePullback_of_hasLocallyFreeRank
    (p : Y ⟶ X) [IsFinite p.left] [IsDominant p.left]
    (d : ℕ) (hd : Scheme.Hom.HasLocallyFreeRank p.left d)
    (DX : Set X.left) (hfinX : DX.Finite)
    (hclosedX : ∀ x ∈ DX, IsClosed ({x} : Set X.left))
    (DY : Set Y.left) (hfinY : DY.Finite)
    (hclosedY : ∀ y ∈ DY, IsClosed ({y} : Set Y.left))
    {U V : Scheme.{u}} (jU : U ⟶ X.left) [IsOpenImmersion jU] (hDX : Set.range jU = DXᶜ)
    (jV : V ⟶ Y.left) [IsOpenImmersion jV] (hDY : Set.range jV = DYᶜ)
    (f : V ⟶ U) (hsq : IsPullback jV f p.left jU)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    (compactSupportTraceAddEquiv Y hY DY hfinY hclosedY jV hDY n hn hunit
      (levelInvertible p.left n hinv)).toAddMonoidHom.comp
        (CompactSupport.finiteRootsPullbackMap p.left f jU jV hsq n 2) =
      d • (compactSupportTraceAddEquiv X hX DX hfinX hclosedX jU hDX n hn hunit
        hinv).toAddMonoidHom := by
  change ((traceAddEquiv hY n hn hunit (levelInvertible p.left n hinv)).toAddMonoidHom.comp
      (CompactSupport.rootsMap jV n hn (levelInvertible p.left n hinv) 2)).comp _ =
    d • ((traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
      (CompactSupport.rootsMap jU n hn hinv 2))
  rw [AddMonoidHom.comp_assoc,
    CompactSupport.rootsMap_finiteRootsPullback p.left f jU jV hsq n hn hinv 2,
    ← AddMonoidHom.comp_assoc,
    traceAddEquiv_pullback_of_hasLocallyFreeRank hX hY p d hd n hn hunit hinv]
  apply AddMonoidHom.ext
  intro x
  rfl

/-- The original finite-etale transfer preserves the original normalized compact
trace on connected covers, including degrees sharing prime factors with the
coefficient level. Completion degree and positivity are derived from the actual
dense-open square, not supplied as rank-matching assumptions. -/
theorem compactSupportTraceAddEquiv_finiteRootsTrace
    (p : Y ⟶ X) [IsFinite p.left] [IsDominant p.left]
    (DX : Set X.left) (hfinX : DX.Finite)
    (hclosedX : ∀ x ∈ DX, IsClosed ({x} : Set X.left))
    (DY : Set Y.left) (hfinY : DY.Finite)
    (hclosedY : ∀ y ∈ DY, IsClosed ({y} : Set Y.left))
    {U V : Scheme.{u}} [Nonempty U] [Nonempty V]
    (jU : U ⟶ X.left) [IsOpenImmersion jU] (hDX : Set.range jU = DXᶜ)
    (jV : V ⟶ Y.left) [IsOpenImmersion jV] (hDY : Set.range jV = DYᶜ)
    (f : V ⟶ U) [Etale f] (hsq : IsPullback jV f p.left jU)
    (d : ℕ) (hd : ∀ x : U, f.finrank x = d)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    (compactSupportTraceAddEquiv X hX DX hfinX hclosedX jU hDX n hn hunit
      hinv).toAddMonoidHom.comp
        (CompactSupport.finiteRootsTraceMap p.left f jU jV hsq d hd n hn
          (levelInvertible jU n hinv) 2) =
      (compactSupportTraceAddEquiv Y hY DY hfinY hclosedY jV hDY n hn hunit
        (levelInvertible p.left n hinv)).toAddMonoidHom := by
  classical
  let := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  let := Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hY
  let : IsIntegral U := isIntegral_of_isOpenImmersion jU
  let : IsIntegral V := isIntegral_of_isOpenImmersion jV
  let : IsFinite f := MorphismProperty.of_isPullback hsq (inferInstance : IsFinite p.left)
  let : IsDominant f := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace f f.isOpenMap⟩
  have hfinf := Scheme.Hom.FiniteFlat.functionField_finite f
    Scheme.Modules.affineModuleBaseChange Scheme.Hom.FiniteFlat.finiteDominantGenericFibre
    (Scheme.Hom.finiteLocallyFree_of_finite_etale
      Scheme.Hom.finiteFlatPresentationLocallyFree f)
  have hfinp := Scheme.FunctionField.finite_of_open_square p.left f jU jV hsq.w.symm hfinf
  have hdegf : Scheme.Hom.FiniteFlat.functionFieldDegree f = d :=
    (Scheme.Hom.FiniteFlat.finrank_eq_functionFieldDegree f (Classical.ofNonempty : U)).symm.trans
      (hd _)
  have hdeg : Scheme.Hom.FiniteFlat.functionFieldDegree p.left = d :=
    (Scheme.FunctionField.finrank_open_square p.left f jU jV hsq.w.symm).trans hdegf
  have hdpos : 0 < d := by
    let := functionFieldMapAlgebra f
    let := hfinf
    rw [← hdegf]
    exact Module.finrank_pos
  have hm : 0 < n ^ d := pow_pos hn d
  have hN : 0 < n ^ d * n := Nat.mul_pos hm hn
  have hunit' : IsUnit ((n ^ d * n : ℕ) : k) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using (hunit.pow d).mul hunit
  have hinv' : IsUnit ((n ^ d * n : ℕ) : Γ(X.left, ⊤)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using (hinv.pow d).mul hinv
  refine trace_eq_of_raised_level n d hn hdpos
    (compactSupportTraceAddEquiv X hX DX hfinX hclosedX jU hDX n hn hunit hinv)
    (compactSupportTraceAddEquiv Y hY DY hfinY hclosedY jV hDY n hn hunit
      (levelInvertible p.left n hinv))
    (compactSupportTraceAddEquiv X hX DX hfinX hclosedX jU hDX (n ^ d * n) hN hunit' hinv')
    (compactSupportTraceAddEquiv Y hY DY hfinY hclosedY jV hDY (n ^ d * n) hN hunit'
      (levelInvertible p.left (n ^ d * n) hinv'))
    (CompactSupport.finiteRootsTraceMap p.left f jU jV hsq d hd n hn
      (levelInvertible jU n hinv) 2)
    (CompactSupport.finiteRootsTraceMap p.left f jU jV hsq d hd (n ^ d * n) hN
      (levelInvertible jU (n ^ d * n) hinv') 2)
    (CompactSupport.finiteRootsPullbackMap p.left f jU jV hsq (n ^ d * n) 2)
    (CompactSupport.H.map jU (rootsLevelMap U (n ^ d) n) 2)
    (CompactSupport.H.map jV (rootsLevelMap V (n ^ d) n) 2) ?_ ?_ ?_ ?_ ?_
  · intro a
    have hp := DFunLike.congr_fun
      (compactSupportTraceAddEquiv_finitePullback_of_functionField_finite hX hY p hfinp
        DX hfinX hclosedX DY hfinY hclosedY jU hDX jV hDY f hsq
        (n ^ d * n) hN hunit' hinv') a
    change compactSupportTraceAddEquiv Y hY DY hfinY hclosedY jV hDY (n ^ d * n)
        hN hunit' (levelInvertible p.left (n ^ d * n) hinv')
          (CompactSupport.finiteRootsPullbackMap p.left f jU jV hsq (n ^ d * n) 2 a) =
      Scheme.Hom.FiniteFlat.functionFieldDegree p.left •
        compactSupportTraceAddEquiv X hX DX hfinX hclosedX jU hDX (n ^ d * n)
          hN hunit' hinv' a at hp
    rw [hdeg] at hp
    exact hp
  · intro a
    exact DFunLike.congr_fun
      (CompactSupport.finiteRootsTraceMap_comp_finiteRootsPullbackMap p.left f jU jV hsq d hd
        (n ^ d * n) hN (levelInvertible jU (n ^ d * n) hinv') 2) a
  · intro a
    exact DFunLike.congr_fun
      (compactSupportTraceAddEquiv_level hX DX hfinX hclosedX jU hDX (n ^ d) n hm hn
        hunit hunit' hinv hinv') a
  · intro b
    exact DFunLike.congr_fun
      (compactSupportTraceAddEquiv_level hY DY hfinY hclosedY jV hDY (n ^ d) n hm hn
        hunit hunit' (levelInvertible p.left n hinv)
          (levelInvertible p.left (n ^ d * n) hinv')) b
  · intro b
    exact DFunLike.congr_fun
      (CompactSupport.finiteRootsTraceMap_level p.left f jU jV hsq d hd (n ^ d) n hm hn
        (levelInvertible jU n hinv) (levelInvertible jU (n ^ d * n) hinv') 2) b

end Curves

end AlgebraicGeometry.Scheme.EtaleCohomology
