/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteLocallyConstant
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Group
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Represented additive coefficients on the small étale site

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen
source basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Sections are actual scheme morphisms into the coefficient group object.
Their additive structure is the additive spelling of the canonical commutative
Hom group. The universe lift is explicit and changes neither sections nor
restriction maps. Subcanonicity is proved from the library's fpqc/pro-étale
subcanonicity; the resulting sheaf and cohomology remain small étale.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u v

/-- The actual big étale topology is subcanonical. -/
theorem etaleSubcanonical : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_proetaleTopology

attribute [local instance] etaleSubcanonical

/-- Restriction from schemes over `X` to étale test schemes is continuous. -/
instance smallEtaleForgetContinuous (X : Scheme.{u}) :
    (Scheme.Etale.forget X).IsContinuous (Scheme.smallEtaleTopology X)
      (Scheme.etaleTopology.over X) := by
  let := flat_of_preservesFiniteLimits (Scheme.Etale.forget X)
  exact Functor.isContinuous_iff_coverPreserving.mpr
    (Functor.coverPreserving_restrictedTopology
      (MorphismProperty.Over.forget @Etale ⊤ X) (Scheme.etaleTopology.over X))

/-- The actual small étale topology is subcanonical. -/
theorem smallEtaleSubcanonical (X : Scheme.{u}) :
    (Scheme.smallEtaleTopology X).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful
    (Scheme.Etale.forget X) _ (Scheme.etaleTopology.over X)

variable {X : Scheme.{u}}

/-- The additive group of sections of a commutative group scheme over an
actual test scheme, lifted to the coefficient universe. -/
-- Keep commutativity as part of the original represented-coefficient section interface.
@[nolint unusedArguments]
abbrev RepresentedSections (H : Grp (Over X)) [IsCommMonObj H.X] (U : Over X) :=
  ULift.{u + 1} (Additive (U ⟶ H.X))

/-- The presheaf of actual sections, with its group-object addition. -/
def representedPresheaf (H : Grp (Over X)) [IsCommMonObj H.X] :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of (RepresentedSections H ((Scheme.Etale.forget X).obj U.unop))
  map f := AddCommGrpCat.ofHom {
    toFun s := ⟨Additive.ofMul ((Scheme.Etale.forget X).map f.unop ≫ s.down.toMul)⟩
    map_zero' := by
      apply ULift.ext
      exact congrArg Additive.ofMul (MonObj.comp_one (M := H.X) _)
    map_add' s t := by
      apply ULift.ext
      exact congrArg Additive.ofMul (MonObj.comp_mul _ s.down.toMul t.down.toMul) }
  map_id U := by ext s; simp
  map_comp f g := by ext s; simp [Category.assoc]

/-- The canonical presheaf of sections is an actual small-étale sheaf. -/
theorem representedPresheaf_isSheaf (H : Grp (Over X)) [IsCommMonObj H.X] :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (representedPresheaf H) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat.{u + 1})]
  change Presheaf.IsSheaf (Scheme.smallEtaleTopology X)
    ((Scheme.Etale.forget X).op ⋙ yoneda.obj H.X ⋙ uliftFunctor.{u + 1})
  apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
  apply Presheaf.isSheaf_comp_of_isSheaf
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The represented additive coefficient sheaf. This construction itself does
not require finiteness; finite étale coefficient objects are included. -/
def representedSheaf (H : Grp (Over X)) [IsCommMonObj H.X] :
    AbelianSheaf.{u, u + 1} X :=
  ⟨representedPresheaf H, representedPresheaf_isSheaf H⟩

/-- A genuine group-scheme map induces an additive sheaf map by postcomposition. -/
def representedSheafMap {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (q : H ⟶ K) : representedSheaf H ⟶ representedSheaf K where
  hom := {
    app U := AddCommGrpCat.ofHom {
      toFun s := ⟨Additive.ofMul (s.down.toMul ≫ q.hom.hom)⟩
      map_zero' := by
        apply ULift.ext
        exact congrArg Additive.ofMul (MonObj.one_comp q.hom.hom)
      map_add' s t := by
        apply ULift.ext
        exact congrArg Additive.ofMul (MonObj.mul_comp s.down.toMul t.down.toMul q.hom.hom) }
    naturality {U V} f := by
      ext s
      change ULift.up (Additive.ofMul (((Scheme.Etale.forget X).map f.unop ≫ s.down.toMul) ≫
        q.hom.hom)) =
        ULift.up (Additive.ofMul ((Scheme.Etale.forget X).map f.unop ≫ (s.down.toMul ≫ q.hom.hom)))
      rw [Category.assoc] }

@[simp] theorem representedSheafMap_id (H : Grp (Over X)) [IsCommMonObj H.X] :
    representedSheafMap (𝟙 H) = 𝟙 (representedSheaf H) := by
  ext U s
  change ULift.up (Additive.ofMul (s.down.toMul ≫ 𝟙 H.X)) = s
  cases s
  simp

@[simp] theorem representedSheafMap_comp {H K L : Grp (Over X)}
    [IsCommMonObj H.X] [IsCommMonObj K.X] [IsCommMonObj L.X]
    (q : H ⟶ K) (r : K ⟶ L) :
    representedSheafMap (q ≫ r) = representedSheafMap q ≫ representedSheafMap r := by
  ext U s
  change ULift.up (Additive.ofMul (s.down.toMul ≫ (q.hom.hom ≫ r.hom.hom))) =
    ULift.up (Additive.ofMul ((s.down.toMul ≫ q.hom.hom) ≫ r.hom.hom))
  rw [Category.assoc]

/-- An actual group-scheme power identity annihilates every section and hence
the represented additive sheaf. -/
theorem representedSheaf_killedBy_of_identity_pow (H : Grp (Over X))
    [IsCommMonObj H.X] (n : ℕ) (h : (𝟙 H.X : H.X ⟶ H.X) ^ n = 1) :
    KilledBy n (representedSheaf H) := by
  ext U t
  change n • t = 0
  apply ULift.ext
  change Additive.ofMul (t.down.toMul ^ n) = Additive.ofMul 1
  apply congrArg Additive.ofMul
  calc
    t.down.toMul ^ n = t.down.toMul ≫ (𝟙 H.X : H.X ⟶ H.X) ^ n := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = 1 := by rw [h, MonObj.comp_one]

section FiniteDescent
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite forget)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
variable {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- Equality of finite étale scheme maps can be checked on the actual fibre,
under the stated Galois-category and fibre-functor hypotheses. -/
theorem finiteEtale_hom_ext {Y Z : Over X}
    [IsFinite Y.hom] [Etale Y.hom] [IsFinite Z.hom] [Etale Z.hom]
    (f g : Y ⟶ Z) (h : ∀ p : Over.mk s ⟶ Y, p ≫ f = p ≫ g) : f = g := by
  let Y' : Scheme.FiniteEtale X := ⟨Y, inferInstance, inferInstance⟩
  let Z' : Scheme.FiniteEtale X := ⟨Z, inferInstance, inferInstance⟩
  let f' : Y' ⟶ Z' := ObjectProperty.homMk f
  let g' : Y' ⟶ Z' := ObjectProperty.homMk g
  have e : f' = g' := (fiberToFinite s).map_injective (FintypeCat.hom_ext _ _ h)
  exact congrArg (fun q : Y' ⟶ Z' => q.hom) e

/-- A commutative marked fibre forces actual group-scheme commutativity. -/
theorem isCommMonObj_of_fiber (H : Grp (Over X))
    [IsFinite H.X.hom] [Etale H.X.hom]
    (h : ∀ p q : Over.mk s ⟶ H.X, p * q = q * p) : IsCommMonObj H.X where
  mul_comm := by
    have : IsFinite (H.X ⊗ H.X).hom := by
      change IsFinite (Limits.pullback.fst H.X.hom H.X.hom ≫ H.X.hom)
      infer_instance
    have : Etale (H.X ⊗ H.X).hom := by
      change Etale (Limits.pullback.fst H.X.hom H.X.hom ≫ H.X.hom)
      infer_instance
    apply finiteEtale_hom_ext s
    intro p
    have hp : p = lift (p ≫ fst H.X H.X) (p ≫ snd H.X H.X) := by simp
    rw [hp, ← Category.assoc, lift_braiding_hom]
    exact h _ _

/-- An annihilator on the faithful geometric fibre is an equality of actual
group-scheme morphisms. -/
theorem identity_pow_eq_one_of_fiber (H : Grp (Over X))
    [IsFinite H.X.hom] [Etale H.X.hom] (n : ℕ)
    (h : ∀ p : Over.mk s ⟶ H.X, p ^ n = 1) : (𝟙 H.X : H.X ⟶ H.X) ^ n = 1 := by
  apply finiteEtale_hom_ext s
  intro p
  rw [MonObj.comp_pow, Category.comp_id, MonObj.comp_one]
  exact h p

open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]

/-- Descending an additive module gives an actually commutative group scheme. -/
instance moduleScheme_comm : IsCommMonObj (moduleScheme s M).X :=
  isCommMonObj_of_fiber s _ fun p q => (moduleFiberMulEquiv s M).injective (by simp [mul_comm])

/-- Module annihilation descends to the identity power morphism. -/
theorem moduleScheme_identity_pow_eq_one (n : ℕ) (h : ∀ m : M, n • m = 0) :
    (𝟙 (moduleScheme s M).X : (moduleScheme s M).X ⟶ (moduleScheme s M).X) ^ n = 1 := by
  apply identity_pow_eq_one_of_fiber s
  intro p
  apply (moduleFiberMulEquiv s M).injective
  rw [map_pow, map_one]
  exact congrArg Multiplicative.ofAdd (h (moduleFiberMulEquiv s M p).toAdd)

/-- The genuine descended additive coefficient sheaf. -/
def moduleSheaf : AbelianSheaf.{u, u + 1} X := representedSheaf (moduleScheme s M)

/-- Module annihilation holds on the actual represented additive sheaf. -/
theorem moduleSheaf_killedBy (n : ℕ) (h : ∀ m : M, n • m = 0) :
    KilledBy n (moduleSheaf s M) :=
  representedSheaf_killedBy_of_identity_pow _ n (moduleScheme_identity_pow_eq_one s M n h)
end FiniteDescent

section Fibre
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable (H : Grp (Over X)) [IsCommMonObj H.X]

/-- Precomposition of actual scheme sections, as an additive homomorphism. -/
def representedSectionsPullback {U V : Over X} (f : U ⟶ V) :
    RepresentedSections H V →+ RepresentedSections H U where
  toFun t := ⟨Additive.ofMul (f ≫ t.down.toMul)⟩
  map_zero' := by
    apply ULift.ext
    exact congrArg Additive.ofMul (MonObj.comp_one (M := H.X) f)
  map_add' t t' := by
    apply ULift.ext
    exact congrArg Additive.ofMul (MonObj.comp_mul f t.down.toMul t'.down.toMul)

/-- Evaluation from the actual geometric sheaf fibre. The map is descended
from the defining filtered colimit, by composing germs with their points. -/
def representedFiberEvaluation :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj (representedSheaf H) ⟶
      AddCommGrpCat.of (RepresentedSections H (Over.mk s)) :=
  (Scheme.pointSmallEtale s).presheafFiberDesc
    (fun U p => AddCommGrpCat.ofHom (representedSectionsPullback H p))
    (by
      intro U V f p
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro t
      change ULift.up (Additive.ofMul (p ≫ ((Scheme.Etale.forget X).map f ≫ t.down.toMul))) =
        ULift.up (Additive.ofMul ((p ≫ (Scheme.Etale.forget X).map f) ≫ t.down.toMul))
      rw [Category.assoc])

@[simp] theorem representedFiberEvaluation_germ (U : X.Etale)
    (p : Over.mk s ⟶ (Scheme.Etale.forget X).obj U)
    (t : RepresentedSections H ((Scheme.Etale.forget X).obj U)) :
    representedFiberEvaluation s H
      ((Scheme.pointSmallEtale s).toPresheafFiber U p (representedPresheaf H) t) =
      ULift.up (Additive.ofMul (p ≫ t.down.toMul)) := by
  have h := (Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberDesc
    (P := representedPresheaf H)
    (fun U p => AddCommGrpCat.ofHom (representedSectionsPullback H p))
    (X := U) (x := p)
  exact ConcreteCategory.congr_hom h t

variable [Etale H.X.hom]

/-- A geometric point gives a germ of the identity section over the étale
coefficient scheme itself. -/
def representedFiberGerm (p : RepresentedSections H (Over.mk s)) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj (representedSheaf H) :=
  (Scheme.pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk H.X.hom) p.down.toMul
    (representedPresheaf H) (ULift.up (Additive.ofMul (𝟙 H.X)))

@[simp] theorem representedFiberEvaluation_germ_self (p : RepresentedSections H (Over.mk s)) :
    representedFiberEvaluation s H (representedFiberGerm s H p) = p := by
  rw [representedFiberGerm, representedFiberEvaluation_germ]
  apply ULift.ext
  change Additive.ofMul (p.down.toMul ≫ 𝟙 H.X) = p.down
  rw [Category.comp_id]
  rfl

theorem representedFiberGerm_evaluation (t :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj (representedSheaf H)) :
    representedFiberGerm s H (representedFiberEvaluation s H t) = t := by
  let : Limits.PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u +
    1}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨U, p, t, rfl⟩ := (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective (P :=
    representedPresheaf H) t
  rw [representedFiberEvaluation_germ]
  let f : U ⟶ Scheme.Etale.mk H.X.hom :=
    MorphismProperty.Over.homMk t.down.toMul.left (Over.w t.down.toMul) (by trivial)
  have e := (Scheme.pointSmallEtale s).toPresheafFiber_w f p (representedPresheaf H)
  have h := ConcreteCategory.congr_hom e (ULift.up (Additive.ofMul (𝟙 H.X)))
  change (Scheme.pointSmallEtale s).toPresheafFiber U p (representedPresheaf H)
      (ULift.up (Additive.ofMul (t.down.toMul ≫ 𝟙 H.X))) = _ at h
  have hf : (Scheme.Etale.forget X).map f = t.down.toMul := by ext; rfl
  change (Scheme.pointSmallEtale s).toPresheafFiber U p (representedPresheaf H)
      (ULift.up (Additive.ofMul (t.down.toMul ≫ 𝟙 H.X))) =
    (Scheme.pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk H.X.hom)
      (p ≫ (Scheme.Etale.forget X).map f) (representedPresheaf H)
      (ULift.up (Additive.ofMul (𝟙 H.X))) at h
  rw [hf, Category.comp_id] at h
  change (Scheme.pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk H.X.hom)
      (p ≫ t.down.toMul) (representedPresheaf H) (ULift.up (Additive.ofMul (𝟙 H.X))) = _
  cases t
  exact h.symm

/-- The actual small-étale stalk of an étale represented commutative group
sheaf is the lifted additive group of its geometric scheme-valued points. -/
def representedFiberIso :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj (representedSheaf H) ≅
      AddCommGrpCat.of (RepresentedSections H (Over.mk s)) :=
  AddEquiv.toAddCommGrpIso (AddEquiv.ofBijective (representedFiberEvaluation s H).hom
    ⟨Function.LeftInverse.injective (representedFiberGerm_evaluation s H),
      Function.RightInverse.surjective (representedFiberEvaluation_germ_self s H)⟩)

end Fibre

section ModuleFibre
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open scoped CategoryTheory.PreGaloisCategory
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (Scheme.FiniteEtale.fiberToFinite s)]
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]

/-- The actual geometric fibre, formed using the small-étale point colimit. -/
abbrev moduleSheafFiber :=
  ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj (moduleSheaf s M)

/-- The genuine stalk marking, composed with the existing scheme-fibre
marking and the proved universe/additive transports. -/
def moduleSheafFiberMarking : moduleSheafFiber s M ≃+ M :=
  (Iso.addCommGroupIsoToAddEquiv (representedFiberIso s (moduleScheme s M))).trans
    (AddEquiv.ulift.trans (moduleFiberMulEquiv s M).toAdditiveLeft)

@[simp] theorem moduleSheafFiberMarking_apply (t : moduleSheafFiber s M) :
    moduleSheafFiberMarking s M t =
      (moduleFiberMulEquiv s M (representedFiberEvaluation s (moduleScheme s M)
        t).down.toMul).toAdd := rfl

/-- Fibre action transported through the genuine stalk marking. The theorem
`moduleSheafFiberAction_evaluation` identifies it with actual fibre-automorphism
evaluation, so it is tied to the constructed finite-étale fibre action. -/
abbrev moduleSheafFiberAction : DistribMulAction (FiberAutGroup s) (moduleSheafFiber s M) :=
  let e := moduleSheafFiberMarking s M
  { e.toEquiv.mulAction (FiberAutGroup s) with
    smul_zero a := by
      change e.symm (a • e 0) = 0
      simp
    smul_add a t t' := by
      change e.symm (a • e (t + t')) = e.symm (a • e t) + e.symm (a • e t')
      simp [smul_add] }

attribute [local instance] moduleSheafFiberAction

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF]
theorem moduleSheafFiberMarking_smul (a : FiberAutGroup s) (t : moduleSheafFiber s M) :
    moduleSheafFiberMarking s M (a • t) = a • moduleSheafFiberMarking s M t :=
  (moduleSheafFiberMarking s M).apply_symm_apply _

/-- Under the proved stalk comparison, the action is precisely evaluation
of the actual finite-étale fibre automorphism at the descended cover. -/
theorem moduleSheafFiberAction_evaluation (a : FiberAutGroup s) (t : moduleSheafFiber s M) :
    (representedFiberEvaluation s (moduleScheme s M) (a • t)).down.toMul =
      a.hom.app (groupCover s (Multiplicative M))
        (representedFiberEvaluation s (moduleScheme s M) t).down.toMul := by
  apply (moduleFiberMulEquiv s M).injective
  rw [moduleFiber_action]
  have h := moduleSheafFiberMarking_smul s M a t
  exact congrArg Multiplicative.ofAdd h

/-- The actual stalk is finite, by its proved additive marking. -/
theorem moduleSheafFiber_finite : Finite (moduleSheafFiber s M) :=
  Finite.of_equiv M (moduleSheafFiberMarking s M).symm.toEquiv

/-- Finite coefficient stalks are given their discrete topology. -/
abbrev moduleSheafFiberTopology : TopologicalSpace (moduleSheafFiber s M) := ⊥
attribute [local instance] moduleSheafFiberTopology

instance moduleSheafFiber_discreteTopology : DiscreteTopology (moduleSheafFiber s M) := ⟨rfl⟩

/-- The genuine finite stalk action is continuous for the evaluation topology
on the actual fibre automorphism group and the discrete coefficient topology. -/
theorem moduleSheafFiber_continuousSMul :
    ContinuousSMul (FiberAutGroup s) (moduleSheafFiber s M) where
  continuous_smul :=
    (continuous_of_discreteTopology : Continuous (moduleSheafFiberMarking s M).symm).comp
      (continuous_smul.comp (continuous_fst.prodMk
        ((continuous_of_discreteTopology : Continuous (moduleSheafFiberMarking s M)).comp
          continuous_snd)))
end ModuleFibre

section FiberNaturality
variable {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)

@[simp] theorem representedSheafMap_app {H H' : Grp (Over X)}
    [IsCommMonObj H.X] [IsCommMonObj H'.X] (q : H ⟶ H') (U : X.Etaleᵒᵖ)
    (t : (representedSheaf H).obj.obj U) :
    (representedSheafMap q).hom.app U t = ULift.up (Additive.ofMul (t.down.toMul ≫ q.hom.hom)) :=
      rfl

/-- The actual stalk comparison sends every induced coefficient morphism to
postcomposition by the same group-scheme map. -/
theorem representedFiberEvaluation_naturality {H H' : Grp (Over X)}
    [IsCommMonObj H.X] [IsCommMonObj H'.X] (q : H ⟶ H')
    (t : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj (representedSheaf
      H)) :
    representedFiberEvaluation s H'
        (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          (representedSheafMap q) t) =
      ULift.up (Additive.ofMul ((representedFiberEvaluation s H t).down.toMul ≫ q.hom.hom)) := by
  let : Limits.PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u +
    1}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨U, p, t, rfl⟩ :=
    (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective (P := representedPresheaf H) t
  let q' : representedPresheaf H ⟶ representedPresheaf H' := (representedSheafMap q).hom
  change representedFiberEvaluation s H'
      ((Scheme.pointSmallEtale s).presheafFiber.map q'
        ((Scheme.pointSmallEtale s).toPresheafFiber U p (representedPresheaf H) t)) = _
  have e := ConcreteCategory.congr_hom
    ((Scheme.pointSmallEtale s).toPresheafFiber_naturality q' U p) t
  change (Scheme.pointSmallEtale s).presheafFiber.map q'
      ((Scheme.pointSmallEtale s).toPresheafFiber U p (representedPresheaf H) t) =
    (Scheme.pointSmallEtale s).toPresheafFiber U p (representedPresheaf H') (q'.app (op U) t) at e
  rw [e, representedFiberEvaluation_germ, representedFiberEvaluation_germ]
  change ULift.up (Additive.ofMul (p ≫ (t.down.toMul ≫ q.hom.hom))) =
    ULift.up (Additive.ofMul ((p ≫ t.down.toMul) ≫ q.hom.hom))
  rw [Category.assoc]
end FiberNaturality

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 1ad9ea0af6a56dc35d5141b9c2bc6549f830ed5d0d468c13b7e141b1b503c617.
Definitions, hypotheses and universes are retained modulo native names. -/
