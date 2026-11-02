/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Stalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.OpenCounitStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleTraceNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LevelMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsSquare
public import Aglib.CategoryTheory.Sites.SheafCohomology.Nsmul
public import Aglib.CategoryTheory.Adjunction.LowerShriekExchange
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange

/-!
# Finite pushforward through an actual open Cartesian square

Finite direct image of extension by zero is supported on the target open.
The original open counit is therefore invertible on this direct image. The
original finite base-change map and open unit identify its restriction, giving
the whole natural comparison before applying ordinary cohomology. The finite
completion map can be ramified and need not be flat or étale.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u wX wY

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

open CoefficientStalkBaseChange
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

variable {V U Y X : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
  (f : V ⟶ U) (jU : U ⟶ X) [IsOpenImmersion jU]
  (jV : V ⟶ Y) [IsOpenImmersion jV]

omit [IsOpenImmersion jU] in
/-- A finite direct image of extension by zero has zero stalk outside the
target open whenever the original structural square commutes. -/
theorem isZero_finiteDirectImage_lowerShriek_stalk_of_not_mem
    (h : jV ≫ p = f ≫ jU) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X) (hη : η default ∉ Set.range jU)
    (M : AbelianSheaf.{u, u + 1} V) :
    IsZero (coefficientFiber η ((directImage p).obj ((etaleLowerShriek jV).obj M))) := by
  let I := {ζ : Spec (.of Ω) ⟶ Y // ζ ≫ p = η}
  have hz (ζ : I) : IsZero (coefficientFiber ζ.val ((etaleLowerShriek jV).obj M)) := by
    apply isZero_etaleLowerShriek_stalk_of_not_mem jV ζ.val _ M
    rintro ⟨v, hv⟩
    apply hη
    refine ⟨f v, ?_⟩
    calc
      jU (f v) = p (jV v) := (congrArg (fun g : V ⟶ X => g v) h).symm
      _ = p (ζ.val default) := congrArg p hv
      _ = η default := congrArg (fun g : Spec (.of Ω) ⟶ X => g default) ζ.property
  let : ∀ ζ : I, Subsingleton (coefficientFiber ζ.val ((etaleLowerShriek jV).obj M)) :=
    fun ζ => AddCommGrpCat.subsingleton_of_isZero (hz ζ)
  have hzero : IsZero (directImageEvaluationTupleTarget p η ((etaleLowerShriek jV).obj M)) := by
    unfold directImageEvaluationTupleTarget
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact hzero.of_iso (Finite.finiteDirectImageEvaluationIso p η ((etaleLowerShriek jV).obj M))

/-- The original open counit is invertible on the actual finite direct image
of extension by zero. No finite étale ambidexterity is used. -/
theorem finiteOpenCounit_isIso (h : jV ≫ p = f ≫ jU)
    (M : AbelianSheaf.{u, u + 1} V) :
    IsIso ((etaleLowerShriekAdjunction jU).counit.app
      ((directImage p).obj ((etaleLowerShriek jV).obj M))) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 X)
  intro Ω _ _ η _
  by_cases hη : η default ∈ Set.range jU
  · obtain ⟨ζ, hζ⟩ := exists_openImmersion_pointLift jU η hη
    exact etaleLowerShriek_counit_stalk_isIso jU ζ η hζ _
  · have h₁ := isZero_etaleLowerShriek_stalk_of_not_mem jU η hη
      ((inverseImage jU).obj ((directImage p).obj ((etaleLowerShriek jV).obj M)))
    have h₂ := isZero_finiteDirectImage_lowerShriek_stalk_of_not_mem p f jU jV h η hη M
    exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

variable (h : IsPullback jV f p jU)

/-- Restriction of the original finite direct image of extension by zero,
using the original finite exchange and the inverse of the original open unit. -/
def finiteOpenRestrictionIso :
    (etaleLowerShriek jV ⋙ directImage p) ⋙ inverseImage jU ≅ directImage f :=
  letI := Finite.finiteBaseChange_isIso p f jU jV h
  Adjunction.LowerShriekExchange.restrictionIso
    (etaleLowerShriekAdjunction jV) (baseChangeMap p f jU jV h.w.symm)

omit [IsOpenImmersion jU] in
/-- The whole inverse restriction comparison, followed by original finite
exchange, is the original open unit. This fixes all normalization maps. -/
theorem finiteOpenRestrictionIso_inv_baseChange :
    (finiteOpenRestrictionIso p f jU jV h).inv ≫
        (Functor.associator (etaleLowerShriek jV) (directImage p) (inverseImage jU)).hom ≫
        Functor.whiskerLeft (etaleLowerShriek jV) (baseChangeMap p f jU jV h.w.symm) =
      (Functor.leftUnitor (directImage f)).inv ≫
        Functor.whiskerRight (etaleLowerShriekAdjunction jV).unit (directImage f) ≫
        (Functor.associator (etaleLowerShriek jV) (inverseImage jV) (directImage f)).hom := by
  let := Finite.finiteBaseChange_isIso p f jU jV h
  exact Adjunction.LowerShriekExchange.restrictionIso_inv_rightMap
    (etaleLowerShriekAdjunction jV) (baseChangeMap p f jU jV h.w.symm)

omit [IsOpenImmersion jU] in
/-- Evaluating the whole inverse normalization retains the same original unit and exchange. -/
theorem finiteOpenRestrictionIso_inv_baseChange_app (M : AbelianSheaf.{u, u + 1} V) :
    (finiteOpenRestrictionIso p f jU jV h).inv.app M ≫
      (baseChangeMap p f jU jV h.w.symm).app ((etaleLowerShriek jV).obj M) =
        (directImage f).map ((etaleLowerShriekAdjunction jV).unit.app M) := by
  have hwhole := NatTrans.congr_app (finiteOpenRestrictionIso_inv_baseChange p f jU jV h) M
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id] using hwhole

/-- The whole finite/open exchange is the mate of the original restriction
comparison under the original target-open adjunction. -/
def finiteLowerShriekDirectImageMap :
    directImage f ⋙ etaleLowerShriek jU ⟶ etaleLowerShriek jV ⋙ directImage p :=
  letI := Finite.finiteBaseChange_isIso p f jU jV h
  Adjunction.LowerShriekExchange.comparison
    (etaleLowerShriekAdjunction jU) (etaleLowerShriekAdjunction jV)
    (baseChangeMap p f jU jV h.w.symm)

/-- The entire mate retains the original unit equation, before coefficient evaluation. -/
theorem finiteLowerShriekDirectImageMap_unit :
    (Functor.rightUnitor (directImage f)).inv ≫
      Functor.whiskerLeft (directImage f) (etaleLowerShriekAdjunction jU).unit ≫
      (Functor.associator (directImage f) (etaleLowerShriek jU) (inverseImage jU)).inv ≫
      Functor.whiskerRight (finiteLowerShriekDirectImageMap p f jU jV h) (inverseImage jU) =
        (finiteOpenRestrictionIso p f jU jV h).inv := by
  let := Finite.finiteBaseChange_isIso p f jU jV h
  exact Adjunction.LowerShriekExchange.comparison_unit
    (etaleLowerShriekAdjunction jU) (etaleLowerShriekAdjunction jV)
    (baseChangeMap p f jU jV h.w.symm)

/-- The original map is lower shriek of restriction comparison, then the original counit. -/
theorem finiteLowerShriekDirectImageMap_app (M : AbelianSheaf.{u, u + 1} V) :
    (finiteLowerShriekDirectImageMap p f jU jV h).app M =
      (etaleLowerShriek jU).map ((finiteOpenRestrictionIso p f jU jV h).inv.app M) ≫
        (etaleLowerShriekAdjunction jU).counit.app
          ((directImage p).obj ((etaleLowerShriek jV).obj M)) := rfl

/-- The entire original finite/open exchange is invertible. -/
theorem finiteLowerShriekDirectImageMap_isIso :
    IsIso (finiteLowerShriekDirectImageMap p f jU jV h) := by
  have (M : AbelianSheaf.{u, u + 1} V) :
      IsIso ((finiteLowerShriekDirectImageMap p f jU jV h).app M) := by
    rw [finiteLowerShriekDirectImageMap_app]
    let := finiteOpenCounit_isIso p f jU jV h.w M
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Finite pushforward commutes with the original extension by zero in an
actual Cartesian square of opens. -/
def finiteLowerShriekDirectImageIso :
    directImage f ⋙ etaleLowerShriek jU ≅ etaleLowerShriek jV ⋙ directImage p :=
  letI := finiteLowerShriekDirectImageMap_isIso p f jU jV h
  asIso (finiteLowerShriekDirectImageMap p f jU jV h)

/-- The isomorphism retains precisely the constructed original mate. -/
theorem finiteLowerShriekDirectImageIso_hom :
    (finiteLowerShriekDirectImageIso p f jU jV h).hom =
      finiteLowerShriekDirectImageMap p f jU jV h := rfl

/-- Compatible original coefficient transports give the whole compact-to-proper
unit square. The compatibility is the original inverse-image square, not a
trace assumption. Roots supply it by their proved composition law. -/
theorem finiteLowerShriekDirectImageMap_coefficient_unit
    {A : AbelianSheaf.{u, u + 1} X} {B : AbelianSheaf.{u, u + 1} U}
    {C : AbelianSheaf.{u, u + 1} Y} {D : AbelianSheaf.{u, u + 1} V}
    (a : (inverseImage jU).obj A ≅ B) (b : (inverseImage p).obj A ≅ C)
    (c : (inverseImage f).obj B ≅ D) (e : (inverseImage jV).obj C ≅ D)
    (hcoeff : (inverseImage f).map a.inv ≫
      (inverseImageSquareIso p f jU jV h.w.symm).hom.app A ≫
        (inverseImage jV).map b.hom = c.hom ≫ e.inv) :
    (etaleLowerShriek jU).map ((inverseImageAdjunction f).unit.app B) ≫
        (etaleLowerShriek jU).map ((directImage f).map c.hom) ≫
        (finiteLowerShriekDirectImageMap p f jU jV h).app D ≫
        (directImage p).map ((etaleLowerShriek jV).map e.inv ≫
          (etaleLowerShriekAdjunction jV).counit.app C) =
      ((etaleLowerShriek jU).map a.inv ≫ (etaleLowerShriekAdjunction jU).counit.app A) ≫
        (inverseImageAdjunction p).unit.app A ≫ (directImage p).map b.hom := by
  let := Finite.finiteBaseChange_isIso p f jU jV h
  exact Adjunction.LowerShriekExchange.coefficient_unit
    (inverseImageAdjunction p) (inverseImageAdjunction f)
    (etaleLowerShriekAdjunction jU) (etaleLowerShriekAdjunction jV)
    (inverseImageSquareIso p f jU jV h.w.symm).hom
    (baseChangeMap p f jU jV h.w.symm) a b c e hcoeff rfl

/-- The actual roots units and original open counits satisfy the whole finite
compact-to-proper coefficient square. The completion map may ramify. -/
theorem finiteLowerShriekDirectImageMap_roots_unit (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (etaleLowerShriek jU).map (rootsUnit f n) ≫
        (finiteLowerShriekDirectImageMap p f jU jV h).app (mu V n) ≫
        (directImage p).map
          ((etaleLowerShriek jV).map (rootsPullbackIso jV n hn (levelInvertible p n hinv)).inv ≫
            (etaleLowerShriekAdjunction jV).counit.app (mu Y n)) =
      ((etaleLowerShriek jU).map (rootsPullbackIso jU n hn hinv).inv ≫
        (etaleLowerShriekAdjunction jU).counit.app (mu X n)) ≫ rootsUnit p n := by
  have hs := finiteLowerShriekDirectImageMap_coefficient_unit p f jU jV h
    (rootsPullbackIso jU n hn hinv) (rootsPullbackIso p n hn hinv)
    (rootsPullbackIso f n hn (levelInvertible jU n hinv))
    (rootsPullbackIso jV n hn (levelInvertible p n hinv))
    (rootsPullbackIso_square_inv p f jU jV h.w.symm n hn hinv)
  rw [← (etaleLowerShriek jU).map_comp_assoc, rootsPullbackIso_unit,
    rootsPullbackIso_unit] at hs
  exact hs

namespace CompactSupport

variable [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)]

/-- Original compact cohomology of the finite direct image is original compact
cohomology of the source, with independent Ext universes. -/
def finiteDirectImageAddEquiv (M : AbelianSheaf.{u, u + 1} V) (q : ℕ) :
    H jU ((directImage f).obj M) q ≃+ H jV M q :=
  ((Sheaf.functorH X.smallEtaleTopology q).mapIso
      ((finiteLowerShriekDirectImageIso p f jU jV h).app M)).addCommGroupIsoToAddEquiv.trans
    (Finite.finiteCohomologyDirectImageAddEquiv p ((etaleLowerShriek jV).obj M) q)

/-- The entire compact comparison is the original mate followed by the original
finite cohomology comparison. -/
theorem finiteDirectImageAddEquiv_toAddMonoidHom (M : AbelianSheaf.{u, u + 1} V) (q : ℕ) :
    (finiteDirectImageAddEquiv p f jU jV h M q).toAddMonoidHom =
      (Finite.finiteCohomologyDirectImageAddEquiv p
        ((etaleLowerShriek jV).obj M) q).toAddMonoidHom.comp
          (Sheaf.H.map ((finiteLowerShriekDirectImageMap p f jU jV h).app M) q) := rfl

/-- Evaluation retains the original compact-support mate and finite comparison. -/
theorem finiteDirectImageAddEquiv_apply (M : AbelianSheaf.{u, u + 1} V) (q : ℕ)
    (x : H jU ((directImage f).obj M) q) :
    finiteDirectImageAddEquiv p f jU jV h M q x =
      Finite.finiteCohomologyDirectImageAddEquiv p ((etaleLowerShriek jV).obj M) q
        (Sheaf.H.map ((finiteLowerShriekDirectImageMap p f jU jV h).app M) q x) := rfl

/-- The whole compact comparison is natural for original coefficient morphisms. -/
theorem finiteDirectImageAddEquiv_naturality
    {M N : AbelianSheaf.{u, u + 1} V} (a : M ⟶ N) (q : ℕ) :
    (finiteDirectImageAddEquiv p f jU jV h N q).toAddMonoidHom.comp
        (H.map jU ((directImage f).map a) q) =
      (H.map jV a q).comp
        (finiteDirectImageAddEquiv p f jU jV h M q).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  change finiteDirectImageAddEquiv p f jU jV h N q
      (H.map jU ((directImage f).map a) q x) =
    H.map jV a q (finiteDirectImageAddEquiv p f jU jV h M q x)
  rw [finiteDirectImageAddEquiv_apply, finiteDirectImageAddEquiv_apply, H.map_apply, H.map_apply,
    ← Sheaf.H.map_comp_apply]
  change Finite.finiteCohomologyDirectImageAddEquiv p ((etaleLowerShriek jV).obj N) q
      (Sheaf.H.map (((directImage f ⋙ etaleLowerShriek jU).map a) ≫
        (finiteLowerShriekDirectImageMap p f jU jV h).app N) q x) = _
  rw [(finiteLowerShriekDirectImageMap p f jU jV h).naturality a, Sheaf.H.map_comp_apply]
  exact Finite.finiteCohomologyDirectImageAddEquiv_naturality p
    ((etaleLowerShriek jV).map a) q _

/-- Pullback on original compact cohomology through the original finite
inverse-image unit and the actual Cartesian compact-support comparison. -/
def finitePullbackMap (F : AbelianSheaf.{u, u + 1} U) (q : ℕ) :
    H jU F q →+ H jV ((inverseImage f).obj F) q :=
  (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).toAddMonoidHom.comp
    (H.map jU ((inverseImageAdjunction f).unit.app F) q)

/-- Every value retains the original unit, with no alternative cohomology realization. -/
theorem finitePullbackMap_apply (F : AbelianSheaf.{u, u + 1} U) (q : ℕ) (x : H jU F q) :
    finitePullbackMap p f jU jV h F q x =
      finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q
        (H.map jU ((inverseImageAdjunction f).unit.app F) q x) := rfl

/-- The whole original compact pullback commutes with original coefficient maps. -/
theorem finitePullbackMap_naturality {F G : AbelianSheaf.{u, u + 1} U}
    (a : F ⟶ G) (q : ℕ) :
    (finitePullbackMap p f jU jV h G q).comp (H.map jU a q) =
      (H.map jV ((inverseImage f).map a) q).comp
        (finitePullbackMap p f jU jV h F q) := by
  apply AddMonoidHom.ext
  intro x
  change finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj G) q
      (H.map jU ((inverseImageAdjunction f).unit.app G) q (H.map jU a q x)) =
    H.map jV ((inverseImage f).map a) q
      (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q
        (H.map jU ((inverseImageAdjunction f).unit.app F) q x))
  rw [← H.map_comp_apply]
  have hu := (inverseImageAdjunction f).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [hu, H.map_comp_apply]
  exact DFunLike.congr_fun
    (finiteDirectImageAddEquiv_naturality p f jU jV h ((inverseImage f).map a) q)
    (H.map jU ((inverseImageAdjunction f).unit.app F) q x)

/-- Pullback of original compact roots cohomology through the literal roots
unit. Its construction itself allows every level, including zero. -/
def finiteRootsPullbackMap (n q : ℕ) : H jU (mu U n) q →+ H jV (mu V n) q :=
  (finiteDirectImageAddEquiv p f jU jV h (mu V n) q).toAddMonoidHom.comp
    (H.map jU (rootsUnit f n) q)

/-- The entire compact roots pullback commutes with the canonical level maps
before any positive-invertible coefficient comparison is used. -/
theorem finiteRootsPullbackMap_level (m n q : ℕ) :
    (finiteRootsPullbackMap p f jU jV h n q).comp (H.map jU (rootsLevelMap U m n) q) =
      (H.map jV (rootsLevelMap V m n) q).comp
        (finiteRootsPullbackMap p f jU jV h (m * n) q) := by
  apply AddMonoidHom.ext
  intro x
  change finiteDirectImageAddEquiv p f jU jV h (mu V n) q
      (H.map jU (rootsUnit f n) q (H.map jU (rootsLevelMap U m n) q x)) =
    H.map jV (rootsLevelMap V m n) q
      (finiteDirectImageAddEquiv p f jU jV h (mu V (m * n)) q
        (H.map jU (rootsUnit f (m * n)) q x))
  rw [← H.map_comp_apply, rootsLevelMap_unit, H.map_comp_apply]
  exact DFunLike.congr_fun
    (finiteDirectImageAddEquiv_naturality p f jU jV h (rootsLevelMap V m n) q)
    (H.map jU (rootsUnit f (m * n)) q x)

/-- At a positive invertible level the original roots unit is the original
inverse-image unit followed by its canonical roots comparison. -/
theorem finiteRootsPullbackMap_eq_comp (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(U, ⊤))) (q : ℕ) :
    finiteRootsPullbackMap p f jU jV h n q =
      (H.map jV (rootsPullbackIso f n hn hinv).hom q).comp
        (finitePullbackMap p f jU jV h (mu U n) q) := by
  apply AddMonoidHom.ext
  intro x
  change finiteDirectImageAddEquiv p f jU jV h (mu V n) q
      (H.map jU (rootsUnit f n) q x) =
    H.map jV (rootsPullbackIso f n hn hinv).hom q
      (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj (mu U n)) q
        (H.map jU ((inverseImageAdjunction f).unit.app (mu U n)) q x))
  rw [← rootsPullbackIso_unit f n hn hinv, H.map_comp_apply]
  exact DFunLike.congr_fun
    (finiteDirectImageAddEquiv_naturality p f jU jV h (rootsPullbackIso f n hn hinv).hom q)
    (H.map jU ((inverseImageAdjunction f).unit.app (mu U n)) q x)

variable [Etale f] (d : ℕ) (hd : ∀ x : U, f.finrank x = d)

/-- Transfer on original compact cohomology uses the locally normalized
original sheaf trace and the inverse of the actual finite compact comparison. -/
def finiteTraceMap (F : AbelianSheaf.{u, u + 1} U) (q : ℕ) :
    H jV ((inverseImage f).obj F) q →+ H jU F q :=
  letI : IsFinite f := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  (H.map jU ((finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app F) q).comp
    (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm.toAddMonoidHom

/-- The entire original transfer/pullback composite is multiplication by the
actual finite étale rank. No coprimality or coefficient-torsion premise is used. -/
theorem finiteTraceMap_comp_finitePullbackMap (F : AbelianSheaf.{u, u + 1} U) (q : ℕ) :
    (finiteTraceMap p f jU jV h d hd F q).comp (finitePullbackMap p f jU jV h F q) =
      nsmulAddMonoidHom (α := H jU F q) d := by
  let : IsFinite f := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  have hr := NatTrans.congr_app (finiteEtaleSheafTrace_rank (Scheme.FiniteEtale.mk f) d hd) F
  change (inverseImageAdjunction f).unit.app F ≫
      (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app F = d • 𝟙 F at hr
  apply AddMonoidHom.ext
  intro x
  change H.map jU ((finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app F) q
      ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm
        (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q
          (H.map jU ((inverseImageAdjunction f).unit.app F) q x))) = d • x
  rw [AddEquiv.symm_apply_apply, ← H.map_comp_apply, hr, H.map_apply, Functor.map_nsmul]
  exact (congrArg
    (fun a : (etaleLowerShriek jU).obj F ⟶ (etaleLowerShriek jU).obj F =>
      Sheaf.H.map (d • a) q x) ((etaleLowerShriek jU).map_id F)).trans
    (Sheaf.H.map_nsmul_id_apply ((etaleLowerShriek jU).obj F) q d x)

/-- The whole compact transfer is natural in the original coefficient sheaf. -/
theorem finiteTraceMap_naturality {F G : AbelianSheaf.{u, u + 1} U}
    (a : F ⟶ G) (q : ℕ) :
    (finiteTraceMap p f jU jV h d hd G q).comp (H.map jV ((inverseImage f).map a) q) =
      (H.map jU a q).comp (finiteTraceMap p f jU jV h d hd F q) := by
  let : IsFinite f := MorphismProperty.of_isPullback h (inferInstance : IsFinite p)
  apply AddMonoidHom.ext
  intro x
  have he : (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj G) q).symm
      (H.map jV ((inverseImage f).map a) q x) =
    H.map jU ((directImage f).map ((inverseImage f).map a)) q
      ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm x) := by
    apply (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj G) q).injective
    rw [AddEquiv.apply_symm_apply]
    have hn := DFunLike.congr_fun
      (finiteDirectImageAddEquiv_naturality p f jU jV h ((inverseImage f).map a) q)
      ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm x)
    change finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj G) q
        (H.map jU ((directImage f).map ((inverseImage f).map a)) q
          ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm x)) =
      H.map jV ((inverseImage f).map a) q
        (finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q
          ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm x)) at hn
    rw [AddEquiv.apply_symm_apply] at hn
    exact hn.symm
  change H.map jU ((finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app G) q
      ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj G) q).symm
        (H.map jV ((inverseImage f).map a) q x)) =
    H.map jU a q
      (H.map jU ((finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app F) q
        ((finiteDirectImageAddEquiv p f jU jV h ((inverseImage f).obj F) q).symm x))
  rw [he, ← H.map_comp_apply, ← H.map_comp_apply]
  have ht := (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).naturality a
  change (directImage f).map ((inverseImage f).map a) ≫
      (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app G =
    (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app F ≫ a at ht
  rw [ht]

/-- Transfer of original compact roots cohomology through the same locally
normalized finite trace and the original roots inverse-image comparison. -/
def finiteRootsTraceMap (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(U, ⊤))) (q : ℕ) :
    H jV (mu V n) q →+ H jU (mu U n) q :=
  (finiteTraceMap p f jU jV h d hd (mu U n) q).comp
    (H.map jV (rootsPullbackIso f n hn hinv).inv q)

/-- The whole actual roots transfer/pullback composite is its actual rank,
including composite levels and level one. -/
theorem finiteRootsTraceMap_comp_finiteRootsPullbackMap (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(U, ⊤))) (q : ℕ) :
    (finiteRootsTraceMap p f jU jV h d hd n hn hinv q).comp
        (finiteRootsPullbackMap p f jU jV h n q) =
      nsmulAddMonoidHom (α := H jU (mu U n) q) d := by
  rw [finiteRootsPullbackMap_eq_comp p f jU jV h n hn hinv q]
  apply AddMonoidHom.ext
  intro x
  change finiteTraceMap p f jU jV h d hd (mu U n) q
      (H.map jV (rootsPullbackIso f n hn hinv).inv q
        (H.map jV (rootsPullbackIso f n hn hinv).hom q
          (finitePullbackMap p f jU jV h (mu U n) q x))) = d • x
  rw [← H.map_comp_apply, Iso.hom_inv_id, H.map_id_apply]
  exact DFunLike.congr_fun
    (finiteTraceMap_comp_finitePullbackMap p f jU jV h d hd (mu U n) q) x

/-- The entire actual finite roots transfer commutes with canonical power
reduction in the same abelian-sheaf category, without scalar extension. -/
theorem finiteRootsTraceMap_level (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(U, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(U, ⊤))) (q : ℕ) :
    (finiteRootsTraceMap p f jU jV h d hd n hn hinv q).comp
        (H.map jV (rootsLevelMap V m n) q) =
      (H.map jU (rootsLevelMap U m n) q).comp
        (finiteRootsTraceMap p f jU jV h d hd (m * n) (Nat.mul_pos hm hn) hinv' q) := by
  apply AddMonoidHom.ext
  intro x
  change finiteTraceMap p f jU jV h d hd (mu U n) q
      (H.map jV (rootsPullbackIso f n hn hinv).inv q
        (H.map jV (rootsLevelMap V m n) q x)) =
    H.map jU (rootsLevelMap U m n) q
      (finiteTraceMap p f jU jV h d hd (mu U (m * n)) q
        (H.map jV (rootsPullbackIso f (m * n) (Nat.mul_pos hm hn) hinv').inv q x))
  rw [← H.map_comp_apply, rootsLevelMap_pullback_inv f m n hm hn hinv hinv',
    H.map_comp_apply]
  exact DFunLike.congr_fun
    (finiteTraceMap_naturality p f jU jV h d hd (rootsLevelMap U m n) q)
    (H.map jV (rootsPullbackIso f (m * n) (Nat.mul_pos hm hn) hinv').inv q x)

end CompactSupport

end AlgebraicGeometry.Scheme.EtaleCohomology
