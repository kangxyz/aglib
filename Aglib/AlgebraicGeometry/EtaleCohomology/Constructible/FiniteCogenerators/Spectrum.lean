/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.IntegralStrata
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.NormalGenericModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.Factorization

/-! # Actual finite constant cogenerators on an affine spectrum

The original generic maps on the finite integral covering strata extend through
produced normal integral models. Their actual finite product is monic. Ambient
finite presentability then factors those original maps through finite-generated
algebra stages, which are finite over the base by integrality.

The exported constants are arbitrary finite abelian groups. This interface does
not yet assert a specified modulus on the values or a genuine ZMod-linear mono.
No finite normalization or constructibility-to-presentability implication is
used. The actual scheme maps, constant coefficients and product map are stored.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

/-- An actual monomorphism into a finite product of finite direct images of
finite constants. The value groups have no prescribed modulus in this record. -/
structure FiniteConstantProductEmbedding {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) where
  /-- The actual finite index lies in the scheme universe. -/
  index : Type u
  /-- There are finitely many factors. -/
  [finite_index : Finite index]
  /-- The original finite source schemes. -/
  source : index → Scheme.{u}
  /-- Their actual maps to the original base. -/
  morphism : ∀ i, source i ⟶ X
  /-- Each displayed original map is finite. -/
  [finite_morphism : ∀ i, IsFinite (morphism i)]
  /-- The actual small finite abelian values. -/
  value : index → AddCommGrpCat.{u}
  /-- Every displayed value is finite. -/
  [finite_value : ∀ i, Finite (value i)]
  /-- The actual coefficient morphism into the literal product. -/
  map : F ⟶ ∏ᶜ fun i => (directImage (morphism i)).obj
    (ConstantFinite.coefficient (value i) (source i))
  /-- The original coefficient morphism is a monomorphism. -/
  [mono : Mono map]

attribute [instance] FiniteConstantProductEmbedding.finite_index
  FiniteConstantProductEmbedding.finite_morphism FiniteConstantProductEmbedding.finite_value
  FiniteConstantProductEmbedding.mono

variable {R : Type u} [CommRing R]
  {F : AbelianSheaf.{u, u + 1} (Spec (.of R))}

/-- The actual direct-image targets of the given normal models. -/
def normalModelTargets (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, NormalGenericModel R (t.inclusion i) F) :
    t.index → AbelianSheaf.{u, u + 1} (Spec (.of R)) :=
  fun i => (directImage (Spec.algebraMap R (m i).ringType)).obj
    (ConstantFinite.coefficient (m i).value (Spec (.of (m i).ringType)))

/-- The literal product of the original normal-model extension maps. -/
def normalModelProduct (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, NormalGenericModel R (t.inclusion i) F) :
    F ⟶ ∏ᶜ normalModelTargets t m :=
  Pi.lift (f := normalModelTargets t m) fun i => (m i).extensionMap

/-- Each original product coordinate is the supplied normal-model extension. -/
@[reassoc]
theorem normalModelProduct_π (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, NormalGenericModel R (t.inclusion i) F) (i : t.index) :
    normalModelProduct t m ≫ Pi.π (normalModelTargets t m) i = (m i).extensionMap :=
  Pi.lift_comp_π (f := normalModelTargets t m) (fun i => (m i).extensionMap) i

/-- The actual dominant generic points of the covering strata detect the
original maps, so the original normal-model product is monic. -/
theorem mono_normalModelProduct (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, NormalGenericModel R (t.inclusion i) F) :
    Mono (normalModelProduct t m) where
  right_cancellation {G} a b hab := by
    apply t.fieldPoint_inverseImages_map_injective
      (fun i => (Spec (.of (m i).ringType)).functionField) (fun i => (m i).point) G
    funext i
    change (inverseImage ((m i).point ≫ t.inclusion i)).map a =
      (inverseImage ((m i).point ≫ t.inclusion i)).map b
    rw [(m i).over]
    apply (cancel_mono (m i).trivialization.hom).mp
    apply ((inverseImageAdjunction
      ((Spec (.of (m i).ringType)).fromSpecStalk
        (genericPoint (Spec (.of (m i).ringType))) ≫
          Spec.algebraMap R (m i).ringType)).homEquiv G _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
    let π := Pi.π (normalModelTargets t m) i
    have hp : normalModelProduct t m ≫ π = (m i).extensionMap :=
      normalModelProduct_π t m i
    have hcoord : a ≫ (m i).extensionMap = b ≫ (m i).extensionMap := by
      have hproj : a ≫ (normalModelProduct t m ≫ π) = b ≫ (normalModelProduct t m ≫ π) :=
        (Category.assoc a (normalModelProduct t m) π).symm.trans
          ((congrArg (fun k => k ≫ π) hab).trans
            (Category.assoc b (normalModelProduct t m) π))
      exact (congrArg (fun k => a ≫ k) hp.symm).trans
        (hproj.trans (congrArg (fun k => b ≫ k) hp))
    let N := Spec (.of (m i).ringType)
    let f := Spec.algebraMap R (m i).ringType
    let v := (directImage f).map
      (NormalConstants.constantGenericIso N (ConstantFinite.value (m i).value)).hom ≫
      (directImageCompIso f (N.fromSpecStalk (genericPoint N))).hom.app
        (ConstantFinite.coefficient (m i).value (Spec N.functionField))
    have hfac : (m i).extensionMap ≫ v =
        (inverseImageAdjunction (N.fromSpecStalk (genericPoint N) ≫ f)).homEquiv F _
          (m i).trivialization.hom := (m i).extensionMap_comp
    exact (congrArg (fun k => a ≫ k) hfac.symm).trans
      ((Category.assoc a (m i).extensionMap v).symm.trans
        ((congrArg (fun k => k ≫ v) hcoord).trans
          ((Category.assoc b (m i).extensionMap v).trans
            (congrArg (fun k => b ≫ k) hfac))))

/-- Factorization through original coordinate maps preserves monicity of the
literal product map. All objects and product projections stay abstract here. -/
theorem mono_productLift_of_factors {C : Type*} [Category* C] {ι : Type*}
    {P : C} {A B : ι → C} [HasProduct A] [HasProduct B]
    (a : ∀ i, P ⟶ B i) (b : ∀ i, P ⟶ A i) (c : ∀ i, A i ⟶ B i)
    (h : ∀ i, b i ≫ c i = a i) [Mono (Pi.lift a)] : Mono (Pi.lift b) := by
  have hprod : Pi.lift b ≫ CategoryTheory.Limits.Pi.map c = Pi.lift a := by
    apply Pi.hom_ext
    intro i
    calc
      (Pi.lift b ≫ CategoryTheory.Limits.Pi.map c) ≫ Pi.π B i =
          Pi.lift b ≫ (CategoryTheory.Limits.Pi.map c ≫ Pi.π B i) := Category.assoc _ _ _
      _ = Pi.lift b ≫ (Pi.π A i ≫ c i) :=
        congrArg (fun k => Pi.lift b ≫ k) (Pi.map_π c i)
      _ = (Pi.lift b ≫ Pi.π A i) ≫ c i := (Category.assoc _ _ _).symm
      _ = b i ≫ c i := congrArg (fun k => k ≫ c i) (Pi.lift_comp_π b i)
      _ = a i := h i
      _ = Pi.lift a ≫ Pi.π B i := (Pi.lift_comp_π a i).symm
  exact mono_of_mono_fac hprod

/-- The supplied actual normal models and ambient finite presentability give
finite-stage constant cogenerators, preserving the original cocone arrows. -/
def finiteConstantProductEmbeddingOfModels
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) [IsFinitelyPresentable.{u + 1} F]
    (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, NormalGenericModel R (t.inclusion i) F) : FiniteConstantProductEmbedding F := by
  apply Classical.choice
  have : Finite t.index := t.finite_index
  have hfac (i : t.index) : ∃ (s : Finset (m i).ringType)
      (b : F ⟶ (AffineIntegralConstants.constantPushforwardDiagram R (m i).ringType
        (m i).value).obj (op (op s))),
      b ≫ (AffineIntegralConstants.constantPushforwardCocone R (m i).ringType
        (m i).value).ι.app (op (op s)) = (m i).extensionMap :=
    AffineIntegralConstants.exists_constantPushforward_stage_factorization
      R (m i).ringType (m i).value F (m i).extensionMap
  choose s b hb using hfac
  let A := fun i => (AffineIntegralConstants.constantPushforwardDiagram R (m i).ringType
    (m i).value).obj (op (op (s i)))
  let a (i : t.index) : F ⟶ normalModelTargets t m i := (m i).extensionMap
  let c (i : t.index) : A i ⟶ normalModelTargets t m i :=
    (AffineIntegralConstants.constantPushforwardCocone R (m i).ringType
      (m i).value).ι.app (op (op (s i)))
  let β : F ⟶ ∏ᶜ A := Pi.lift (f := A) b
  have : Mono (Pi.lift a) := mono_normalModelProduct t m
  have hmono : Mono β := mono_productLift_of_factors a b c hb
  let Y := fun i => Spec (.of (Algebra.FiniteTypeSubalgebraLimit.stage R (m i).ringType (s i)))
  let f := fun i => Spec.algebraMap R
    (Algebra.FiniteTypeSubalgebraLimit.stage R (m i).ringType (s i))
  exact ⟨{
    index := t.index
    finite_index := t.finite_index
    source := Y
    morphism := f
    finite_morphism := fun i =>
      AffineIntegralConstants.constantPushforwardStage_isFinite R (m i).ringType (s i)
    value := fun i => (m i).value
    finite_value := fun i => (m i).finite_value
    map := β
    mono := hmono }⟩

/-- A finite integral locally closed cover and ambient finite presentability
produce actual finite constant cogenerators on the original affine spectrum. -/
def finiteConstantProductEmbeddingOfIntegralCover
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) [IsFinitelyPresentable.{u + 1} F]
    (t : FiniteIntegralLocallyClosedCover F) : FiniteConstantProductEmbedding F := by
  have (i : t.index) : IsIntegral (t.stratum i) := t.integral i
  have (i : t.index) : IsImmersion (t.inclusion i) := t.immersion i
  exact finiteConstantProductEmbeddingOfModels F t
    (fun i => normalGenericModel R (t.inclusion i) F (t.locally_constant i))

/-- On a Noetherian affine spectrum, a geometrically constructible coefficient
which is ambient finitely presentable has actual finite constant cogenerators. -/
def finiteConstantProductEmbedding (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) [IsFinitelyPresentable.{u + 1} F]
    (hF : IsConstructible F) : FiniteConstantProductEmbedding F :=
  finiteConstantProductEmbeddingOfIntegralCover F (finiteIntegralLocallyClosedCover F hF)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
