/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedTorsor
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.ContinuousTorsors

/-!
# Descent of actual finite scheme-torsor morphisms from their fibres

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Only the existing Galois-category
and fibre-functor classes are retained. Actual equivariant fibre maps descend
through their proved continuous-action equivalence; faithfulness on an actual
finite product proves equivariance on every scheme-valued point.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleH1.SchemeTorsorClassification
universe u
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)

/-- A nonempty fibre makes the finite étale cover surjective over a
preconnected base, by the nonempty clopen image. No GC/FF assumption is used. -/
theorem surjective_of_nonempty_fiber (Y : Scheme.FiniteEtale X) [PreconnectedSpace X]
    (h : Nonempty (Fiber s Y)) : Surjective Y.obj.hom := by
  obtain ⟨p⟩ := h
  have hcl : IsClopen (Set.range Y.obj.hom) :=
    ⟨Y.obj.hom.isClosedMap.isClosed_range, Y.obj.hom.isOpenMap.isOpen_range⟩
  let k : Spec (CommRingCat.of K) := ⟨⊥, inferInstance⟩
  exact ⟨Set.range_eq_univ.mp (hcl.eq_univ ⟨Y.obj.hom (p.left k), p.left k, rfl⟩)⟩

variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- The faithful geometric fibre of a surjective finite étale cover is
nonempty. Empty fibre would force the actual scheme to be empty. -/
theorem nonempty_fiber_of_surjective (Y : Scheme.FiniteEtale X) [Surjective Y.obj.hom] :
    Nonempty (Fiber s Y) := by
  by_contra h
  have hf : IsEmpty ((fiberToFinite s).obj Y) := ⟨fun p => h ⟨p⟩⟩
  have hY : IsEmpty Y.obj.left :=
    (Scheme.FiniteEtale.Connectedness.isInitial_iff_isEmpty Y).mp
      ((PreGaloisCategory.initial_iff_fiber_empty (fiberToFinite s) Y).mpr hf)
  let k : Spec (CommRingCat.of K) := ⟨⊥, inferInstance⟩
  obtain ⟨y, _⟩ := Y.obj.hom.surjective (s k)
  exact hY.false y

variable {Y Z W : Scheme.FiniteEtale X}

/-- An equivariant map of the actual finite fibres is a morphism of the
actual continuous-action category. -/
def equivariantFiberMap (f : Fiber s Y → Fiber s Z)
    (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      f (γ.hom.app Y x) = γ.hom.app Z (f x)) :
    (classification s).functor.obj Y ⟶ (classification s).functor.obj Z :=
  ObjectProperty.homMk {
    hom := FintypeCat.homMk f
    comm γ := by apply FintypeCat.hom_ext; intro x; exact hf γ x }

/-- Descend an equivariant map of finite fibres to its actual scheme morphism. -/
def descendFiberMap (f : Fiber s Y → Fiber s Z)
    (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      f (γ.hom.app Y x) = γ.hom.app Z (f x)) : Y.obj ⟶ Z.obj :=
  ((classification s).functor.preimage (equivariantFiberMap s f hf)).hom

/-- Evaluation of the descended scheme map is exactly the prescribed map. -/
@[simp] theorem descendFiberMap_fiber (f : Fiber s Y → Fiber s Z)
    (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      f (γ.hom.app Y x) = γ.hom.app Z (f x)) (x : Fiber s Y) :
    x ≫ descendFiberMap s f hf = f x := by
  exact ConcreteCategory.congr_hom (C := FintypeCat)
    (congrArg (fun q => q.hom.hom)
      ((classification s).functor.map_preimage (equivariantFiberMap s f hf))) x

/-- Uniqueness is faithfulness of the actual fibre functor. -/
theorem descendFiberMap_unique (f : Fiber s Y → Fiber s Z)
    (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      f (γ.hom.app Y x) = γ.hom.app Z (f x))
    (q : Y.obj ⟶ Z.obj) (hq : ∀ x : Fiber s Y, x ≫ q = f x) :
    q = descendFiberMap s f hf := by
  apply finiteEtale_hom_ext s
  intro x
  rw [hq, descendFiberMap_fiber]

omit [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)] in
/-- The inverse of an equivariant fibre equivalence is equivariant. -/
theorem fiberEquiv_symm_equivariant (e : Fiber s Y ≃ Fiber s Z)
    (he : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      e (γ.hom.app Y x) = γ.hom.app Z (e x))
    (γ : FiberAutGroup s) (x : Fiber s Z) :
    e.symm (γ.hom.app Z x) = γ.hom.app Y (e.symm x) := by
  apply e.injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

/-- Actual equivariant fibre equivalences descend to actual scheme isomorphisms. -/
def descendFiberIso (e : Fiber s Y ≃ Fiber s Z)
    (he : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      e (γ.hom.app Y x) = γ.hom.app Z (e x)) : Y.obj ≅ Z.obj where
  hom := descendFiberMap s e he
  inv := descendFiberMap s e.symm (fiberEquiv_symm_equivariant s e he)
  hom_inv_id := by
    apply finiteEtale_hom_ext s
    intro x
    simp only [← Category.assoc, descendFiberMap_fiber, Equiv.symm_apply_apply, Category.comp_id]
  inv_hom_id := by
    apply finiteEtale_hom_ext s
    intro x
    simp only [← Category.assoc, descendFiberMap_fiber, Equiv.apply_symm_apply, Category.comp_id]

@[simp] theorem descendFiberIso_hom_fiber (e : Fiber s Y ≃ Fiber s Z)
    (he : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      e (γ.hom.app Y x) = γ.hom.app Z (e x)) (x : Fiber s Y) :
    x ≫ (descendFiberIso s e he).hom = e x := descendFiberMap_fiber s e he x

@[simp] theorem descendFiberIso_inv_fiber (e : Fiber s Y ≃ Fiber s Z)
    (he : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      e (γ.hom.app Y x) = γ.hom.app Z (e x)) (x : Fiber s Z) :
    x ≫ (descendFiberIso s e he).inv = e.symm x :=
  descendFiberMap_fiber s e.symm (fiberEquiv_symm_equivariant s e he) x

/-- A monodromy-equivariant binary fibre map gives a morphism from the actual
finite scheme product. This supplies a product interface for contracted sums. -/
def descendFiberBimap (f : Fiber s Y → Fiber s Z → Fiber s W)
    (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y) (y : Fiber s Z),
      f (γ.hom.app Y x) (γ.hom.app Z y) = γ.hom.app W (f x y)) : Y.obj ⊗ Z.obj ⟶ W.obj :=
  descendFiberMap s (Y := Y ⊗ Z)
    (fun p => f (p ≫ fst Y.obj Z.obj) (p ≫ snd Y.obj Z.obj)) (fun γ p => by
      rw [Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ (Z := Y ⊗ Z) (W := Y)
        (fst Y.obj Z.obj) p |>.symm,
        Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ (Z := Y ⊗ Z) (W := Z)
          (snd Y.obj Z.obj) p |>.symm]
      exact hf γ _ _)

/-- The binary descent evaluates to the original map at every pair of actual fibre points. -/
@[simp] theorem descendFiberBimap_fiber (f : Fiber s Y → Fiber s Z → Fiber s W)
    (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y) (y : Fiber s Z),
      f (γ.hom.app Y x) (γ.hom.app Z y) = γ.hom.app W (f x y))
    (x : Fiber s Y) (y : Fiber s Z) : lift x y ≫ descendFiberBimap s f hf = f x y := by
  unfold descendFiberBimap
  erw [descendFiberMap_fiber s (Y := Y ⊗ Z), lift_fst, lift_snd]

section Actions
variable (A B : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom]
variable (τ : TorsorAction A (toUnit Y.obj)) (σ : TorsorAction B (toUnit Z.obj))
variable (q : A.X ⟶ B.X)
variable (f : Fiber s Y → Fiber s Z)
variable (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
  f (γ.hom.app Y x) = γ.hom.app Z (f x))
variable (hact : ∀ (a : Over.mk s ⟶ A.X) (x : Fiber s Y),
  f (τ.act a x) = σ.act (a ≫ q) (f x))

include hact in
/-- Equivariance on the actual finite fibres is an equality of actual action
morphisms, by faithfulness on the finite coefficient-times-torsor product. -/
theorem descendFiberMap_actionMap :
    τ.actionMap ≫ descendFiberMap s f hf =
      lift (fst A.X Y.obj ≫ q) (snd A.X Y.obj ≫ descendFiberMap s f hf) ≫ σ.actionMap := by
  apply finiteEtale_hom_ext s (Y := (coefficientCover A ⊗ Y).obj) (Z := Z.obj)
  intro p
  calc
    p ≫ (τ.actionMap ≫ descendFiberMap s f hf) =
        τ.act (p ≫ fst A.X Y.obj) (p ≫ snd A.X Y.obj) ≫ descendFiberMap s f hf := by
      rw [← Category.assoc]
      exact congrArg (fun a => a ≫ descendFiberMap s f hf)
        (τ.naturality p (fst A.X Y.obj) (snd A.X Y.obj))
    _ = f (τ.act (p ≫ fst A.X Y.obj) (p ≫ snd A.X Y.obj)) :=
      descendFiberMap_fiber s f hf _
    _ = σ.act ((p ≫ fst A.X Y.obj) ≫ q) (f (p ≫ snd A.X Y.obj)) := hact _ _
    _ = p ≫ (lift (fst A.X Y.obj ≫ q)
        (snd A.X Y.obj ≫ descendFiberMap s f hf) ≫ σ.actionMap) := by
      simp only [σ.comp_actionMap, σ.naturality, ← Category.assoc, descendFiberMap_fiber]

include hact in
/-- Fibre equivariance descends to equivariance on every scheme-valued test
object, not merely on the chosen geometric fibre. -/
theorem descendFiberMap_equivariant {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj) :
    τ.act a x ≫ descendFiberMap s f hf = σ.act (a ≫ q) (x ≫ descendFiberMap s f hf) := by
  have h := congrArg (fun m => lift a x ≫ m)
    (descendFiberMap_actionMap s A B τ σ q f hf hact)
  simpa only [← Category.assoc, τ.comp_actionMap, σ.comp_actionMap, σ.naturality,
    lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using h

end Actions

/-- A fibre equivalence commuting with both monodromy and torsor translation
descends to the actual equivariant scheme isomorphism used by classification. -/
theorem descendFiberIso_equivariant (A B : Grp (Over X))
    [IsFinite A.X.hom] [Etale A.X.hom]
    (τ : TorsorAction A (toUnit Y.obj)) (σ : TorsorAction B (toUnit Z.obj))
    (q : A.X ⟶ B.X) (e : Fiber s Y ≃ Fiber s Z)
    (he : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      e (γ.hom.app Y x) = γ.hom.app Z (e x))
    (hact : ∀ (a : Over.mk s ⟶ A.X) (x : Fiber s Y),
      e (τ.act a x) = σ.act (a ≫ q) (e x))
    {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj) :
    τ.act a x ≫ (descendFiberIso s e he).hom =
      σ.act (a ≫ q) (x ≫ (descendFiberIso s e he).hom) :=
  descendFiberMap_equivariant s A B τ σ q e he hact a x

/-- In particular, monodromy- and translation-equivariant fibre equivalences
of actual surjective scheme torsors give genuine sheaf-torsor isomorphisms. -/
def torsorIsoOfFiberEquiv (A : Grp (Over X)) [IsCommMonObj A.X]
    [IsFinite A.X.hom] [Etale A.X.hom]
    [Surjective Y.obj.hom] [Surjective Z.obj.hom]
    (τ : TorsorAction A (toUnit Y.obj)) (σ : TorsorAction A (toUnit Z.obj))
    (e : Fiber s Y ≃ Fiber s Z)
    (he : ∀ (γ : FiberAutGroup s) (x : Fiber s Y),
      e (γ.hom.app Y x) = γ.hom.app Z (e x))
    (hact : ∀ (a : Over.mk s ⟶ A.X) (x : Fiber s Y), e (τ.act a x) = σ.act a (e x)) :
    Torsor.Iso (torsorOfSchemeAction A Y τ) (torsorOfSchemeAction A Z σ) :=
  torsorOfSchemeActionIso A Y Z τ σ (descendFiberIso s e he) (fun a x => by
    simpa only [Category.comp_id] using descendFiberIso_equivariant s A A τ σ (𝟙 A.X)
      e he (fun a x => by simpa only [Category.comp_id] using hact a x) a x)

section Coordinates
open ContinuousTorsors
open GroupCohomology.ContinuousH1
variable (A : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom]
variable (τ : TorsorAction A (toUnit Y.obj)) (σ : TorsorAction A (toUnit Z.obj))
variable {M : Type u} [AddCommGroup M]
variable (mark : (Over.mk s ⟶ A.X) ≃* Multiplicative M)

/-- Coordinates at actual fibre points produce the unique translation-equivariant
fibre equivalence carrying the selected point to the selected point. -/
def basedFiberEquiv (t : Fiber s Y) (u : Fiber s Z) : Fiber s Y ≃ Fiber s Z :=
  (fibreBasis s A Y τ mark t).trans (fibreBasis s A Z σ mark u).symm

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[simp, nolint simpNF unusedArguments]
theorem basedFiberEquiv_coordinate (t : Fiber s Y) (u : Fiber s Z) (x : Fiber s Y) :
    fibreBasis s A Z σ mark u (basedFiberEquiv s A τ σ mark t u x) =
      fibreBasis s A Y τ mark t x := (fibreBasis s A Z σ mark u).apply_symm_apply _

theorem basedFiberEquiv_translation (t : Fiber s Y) (u : Fiber s Z)
    (a : Over.mk s ⟶ A.X) (x : Fiber s Y) :
    basedFiberEquiv s A τ σ mark t u (τ.act a x) =
      σ.act a (basedFiberEquiv s A τ σ mark t u x) := by
  apply (fibreBasis s A Z σ mark u).injective
  rw [basedFiberEquiv_coordinate, fibreBasis_action, fibreBasis_action,
    basedFiberEquiv_coordinate]

variable [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (hmark : ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X),
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Actual monodromy in torsor coordinates is the literal extracted cocycle
plus the prescribed linear coefficient action. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem fibreBasis_monodromy (t x : Fiber s Y) (γ : FiberAutGroup s) :
    fibreBasis s A Y τ mark t (γ.hom.app Y x) =
      (basedCocycle s A Y τ mark hmark t).val γ + γ • fibreBasis s A Y τ mark t x := by
  have h := rho_affine s A Y τ mark t (MonoidHom.id _) hmark γ 0
    (fibreBasis s A Y τ mark t x)
  change _ = rho s A Y τ mark t γ 0 + _
  simpa only [zero_add, rho_fibre, MonoidHom.id_apply] using h

/-- Equal actual based cocycles make the coordinate equivalence monodromy-equivariant. -/
theorem basedFiberEquiv_monodromy (t : Fiber s Y) (u : Fiber s Z)
    (hc : basedCocycle s A Y τ mark hmark t = basedCocycle s A Z σ mark hmark u)
    (γ : FiberAutGroup s) (x : Fiber s Y) :
    basedFiberEquiv s A τ σ mark t u (γ.hom.app Y x) =
      γ.hom.app Z (basedFiberEquiv s A τ σ mark t u x) := by
  apply (fibreBasis s A Z σ mark u).injective
  rw [basedFiberEquiv_coordinate, fibreBasis_monodromy s A τ mark hmark,
    fibreBasis_monodromy s A σ mark hmark, basedFiberEquiv_coordinate, hc]

/-- Equality in the one common continuous H¹ yields an actual equivariant
scheme isomorphism, after correcting the selected point by the principal change. -/
theorem exists_schemeIso_of_class_eq [Nonempty (Fiber s Y)] [Nonempty (Fiber s Z)]
    (hc : schemeTorsorClass s A Y τ mark hmark = schemeTorsorClass s A Z σ mark hmark) :
    ∃ q : Y.obj ≅ Z.obj, ∀ {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj),
      τ.act a x ≫ q.hom = σ.act a (x ≫ q.hom) := by
  let t : Fiber s Y := Classical.choice inferInstance
  let u : Fiber s Z := Classical.choice inferInstance
  rw [schemeTorsorClass_eq s A Y τ mark hmark t,
    schemeTorsorClass_eq s A Z σ mark hmark u] at hc
  obtain ⟨m, hm⟩ := (classOf_eq_iff _ _ _ _).mp hc
  let u' : Fiber s Z := (fibreBasis s A Z σ mark u).symm m
  have heq : basedCocycle s A Y τ mark hmark t = basedCocycle s A Z σ mark hmark u' := by
    rw [basedCocycle_change s A Z σ mark hmark u u']
    change _ = _ + principal _ _ (fibreBasis s A Z σ mark u ((fibreBasis s A Z σ mark u).symm m))
    rw [Equiv.apply_symm_apply, hm]
    abel
  let e := basedFiberEquiv s A τ σ mark t u'
  have he := basedFiberEquiv_monodromy s A τ σ mark hmark t u' heq
  refine ⟨descendFiberIso s e he, fun {T} a x => ?_⟩
  simpa only [Category.comp_id] using descendFiberIso_equivariant s A A τ σ (𝟙 A.X)
    e he (fun a x => by simpa only [Category.comp_id] using
      basedFiberEquiv_translation s A τ σ mark t u' a x) a x

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Actual equivariant scheme isomorphisms preserve the canonical common-H¹ class. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem schemeTorsorClass_eq_of_schemeIso [Nonempty (Fiber s Y)] [Nonempty (Fiber s Z)]
    (q : Y.obj ≅ Z.obj)
    (hq : ∀ {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj),
      τ.act a x ≫ q.hom = σ.act a (x ≫ q.hom)) :
    schemeTorsorClass s A Y τ mark hmark = schemeTorsorClass s A Z σ mark hmark := by
  have h := schemeTorsorClass_naturality s A Y τ mark hmark A Z σ mark hmark
    (CoefficientMap.id : CoefficientMap (FiberAutGroup s) M M)
    (fun x => x ≫ q.hom)
    (fun a x => by
      simpa only [CoefficientMap.id_apply] using hq (mark.symm (Multiplicative.ofAdd a)) x)
    (fun γ x => (Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ q.hom x).symm)
  simpa only [CoefficientMap.onH1_id, AddMonoidHom.id_apply] using h.symm

/-- The classification criterion is proved for actual finite scheme torsors. -/
theorem schemeTorsorClass_eq_iff [Nonempty (Fiber s Y)] [Nonempty (Fiber s Z)] :
    schemeTorsorClass s A Y τ mark hmark = schemeTorsorClass s A Z σ mark hmark ↔
      ∃ q : Y.obj ≅ Z.obj, ∀ {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj),
        τ.act a x ≫ q.hom = σ.act a (x ≫ q.hom) :=
  ⟨exists_schemeIso_of_class_eq s A τ σ mark hmark,
    fun ⟨q, hq⟩ => schemeTorsorClass_eq_of_schemeIso s A τ σ mark hmark q hq⟩

end Coordinates
section SheafClasses
open ContinuousTorsors
open GroupCohomology.ContinuousH1
variable (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
variable {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ A.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X),
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hR : Stacks03RV X) (hL : IsFiniteLocallyConstant (representedSheaf A))

local instance selectedRepresentativeSurjective (P : Torsor (representedSheaf A)) :
    Surjective (P.finiteEtaleRepresentative hR hL).obj.hom :=
  P.represented_surjective A _ (P.finiteEtaleRepresentativeIso hR hL)

local instance selectedRepresentativeNonempty (P : Torsor (representedSheaf A)) :
    Nonempty (Fiber s (P.finiteEtaleRepresentative hR hL)) :=
  nonempty_fiber_of_surjective s _

/-- The common continuous H¹ class extracted from the actual A3 representative
of a genuine sheaf torsor. No transported or independent H¹ quotient is used. -/
def representedTorsorClass (P : Torsor (representedSheaf A)) : H1 (FiberAutGroup s) M :=
  schemeTorsorClass s A (P.finiteEtaleRepresentative hR hL)
    (P.finiteEtaleSchemeAction A hR hL) mark hmark

/-- Every actual finite étale representation computes this class by its literal
scheme action and its actual monodromy, independently of the chosen representative. -/
theorem representedTorsorClass_eq (P : Torsor (representedSheaf A)) (Y : Scheme.FiniteEtale X)
    [Nonempty (Fiber s Y)] (e : finiteRepresentedSetSheaf Y ≅ P.carrier) :
    representedTorsorClass s A mark hmark hR hL P =
      schemeTorsorClass s A Y (P.representedSchemeAction A Y e) mark hmark := by
  exact schemeTorsorClass_eq_of_schemeIso s A
    (P.finiteEtaleSchemeAction A hR hL) (P.representedSchemeAction A Y e) mark hmark
    (P.representedIso A _ (P.finiteEtaleRepresentativeIso hR hL) P Y (Torsor.Iso.refl P) e)
    (P.representedIso_equivariant A _ (P.finiteEtaleRepresentativeIso hR hL)
      P Y (Torsor.Iso.refl P) e)

/-- The quotient map respects actual equivariant sheaf isomorphisms. -/
theorem representedTorsorClass_iso {P Q : Torsor (representedSheaf A)} (d : P.Iso Q) :
    representedTorsorClass s A mark hmark hR hL P =
      representedTorsorClass s A mark hmark hR hL Q := by
  exact schemeTorsorClass_eq_of_schemeIso s A
    (P.finiteEtaleSchemeAction A hR hL) (Q.finiteEtaleSchemeAction A hR hL) mark hmark
    (P.representedIso A _ (P.finiteEtaleRepresentativeIso hR hL)
      Q _ d (Q.finiteEtaleRepresentativeIso hR hL))
    (P.representedIso_equivariant A _ (P.finiteEtaleRepresentativeIso hR hL)
      Q _ d (Q.finiteEtaleRepresentativeIso hR hL))

/-- The actual canonical torsor-class-to-common-H¹ function. Its additivity is
an independent assertion about the constructed contracted sum. -/
def torsorClassToH1 : TorsorClass (representedSheaf A) → H1 (FiberAutGroup s) M :=
  Quotient.lift (representedTorsorClass s A mark hmark hR hL)
    (fun _ _ ⟨d⟩ => representedTorsorClass_iso s A mark hmark hR hL d)

/-- Explicit quotient representative evaluation. -/
@[simp] theorem torsorClassToH1_mk (P : Torsor (representedSheaf A)) :
    torsorClassToH1 s A mark hmark hR hL (Quotient.mk _ P) =
      representedTorsorClass s A mark hmark hR hL P := rfl

/-- Equal extracted cohomology classes yield actual equivariant sheaf torsors. -/
theorem representedTorsorClass_eq_iff (P Q : Torsor (representedSheaf A)) :
    representedTorsorClass s A mark hmark hR hL P =
      representedTorsorClass s A mark hmark hR hL Q ↔ Nonempty (P.Iso Q) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := exists_schemeIso_of_class_eq s A
      (P.finiteEtaleSchemeAction A hR hL) (Q.finiteEtaleSchemeAction A hR hL) mark hmark h
    let d := torsorOfSchemeActionIso A _ _
      (P.finiteEtaleSchemeAction A hR hL) (Q.finiteEtaleSchemeAction A hR hL) q hq
    exact ⟨(P.representedSchemeActionIso A _ (P.finiteEtaleRepresentativeIso hR hL)).symm.trans
      (d.trans (Q.representedSchemeActionIso A _ (Q.finiteEtaleRepresentativeIso hR hL)))⟩
  · rintro ⟨d⟩
    exact representedTorsorClass_iso s A mark hmark hR hL d

/-- Injectivity follows from actual scheme descent and the proved torsor
isomorphisms, rather than from an assumed cohomological classification. -/
theorem torsorClassToH1_injective :
    Function.Injective (torsorClassToH1 s A mark hmark hR hL) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro P Q h
  exact Quotient.sound ((representedTorsorClass_eq_iff s A mark hmark hR hL P Q).mp h)

/-- A scheme torsor's sheaf has exactly its previously constructed common-H¹ class. -/
theorem representedTorsorClass_of_schemeAction (Y : Scheme.FiniteEtale X) [Surjective Y.obj.hom]
    (τ : TorsorAction A (toUnit Y.obj)) :
    representedTorsorClass s A mark hmark hR hL (torsorOfSchemeAction A Y τ) =
      @schemeTorsorClass _ _ _ s A _ _ Y τ M _ mark _ _ _ _ hmark
        (nonempty_fiber_of_surjective s Y) := by
  let := nonempty_fiber_of_surjective s Y
  rw [representedTorsorClass_eq s A mark hmark hR hL (torsorOfSchemeAction A Y τ) Y (Iso.refl _),
    torsorOfSchemeAction_representedSchemeAction]

end SheafClasses
section ModuleSurjectivity
open ContinuousTorsors
open GroupCohomology.ContinuousH1
variable (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [PreconnectedSpace X]
variable (hR : Stacks03RV X)

/-- The affine zero coordinate is an actual point in the chosen fibre. -/
instance cocycleCover_nonempty (c : Cocycle (FiberAutGroup s) M) :
    Nonempty (Fiber s (cocycleCover s c)) := ⟨cocycleBasepoint s c⟩

/-- The actual finite étale affine torsor of a common continuous cocycle is
surjective, since its literal zero coordinate is an actual fibre point. -/
instance cocycleCover_surjective (c : Cocycle (FiberAutGroup s) M) :
    Surjective (cocycleCover s c).obj.hom :=
  surjective_of_nonempty_fiber s _ ⟨cocycleBasepoint s c⟩

/-- A common continuous cocycle constructs a genuine small-étale sheaf torsor
by affine finite-cover descent and its actual scheme action. -/
def cocycleSheafTorsor (c : Cocycle (FiberAutGroup s) M) : Torsor (moduleSheaf s M) :=
  torsorOfSchemeAction (moduleScheme s M) (cocycleCover s c) (cocycleSchemeAction s c)

/-- Extraction of the class of the constructed sheaf torsor recovers exactly
the class of the original common continuous cocycle. -/
theorem representedTorsorClass_cocycle (c : Cocycle (FiberAutGroup s) M) :
    representedTorsorClass s (moduleScheme s M) (moduleFiberMulEquiv s M)
      (moduleFiber_action s M) hR (moduleSheaf_isFiniteLocallyConstant (s := s) M)
      (cocycleSheafTorsor s M c) = classOf (FiberAutGroup s) M c := by
  change representedTorsorClass s (moduleScheme s M) (moduleFiberMulEquiv s M)
    (moduleFiber_action s M) hR _ (torsorOfSchemeAction _ _ _) = _
  rw [representedTorsorClass_of_schemeAction]
  rw [schemeTorsorClass_eq s (moduleScheme s M) (cocycleCover s c) (cocycleSchemeAction s c)
    (moduleFiberMulEquiv s M) (moduleFiber_action s M) (cocycleBasepoint s c),
    basedCocycle_cocycleSchemeAction]

/-- Every common continuous H¹ class is represented by an actual sheaf torsor
for the descended module sheaf. -/
theorem moduleTorsorClassToH1_surjective :
    Function.Surjective (torsorClassToH1 s (moduleScheme s M) (moduleFiberMulEquiv s M)
      (moduleFiber_action s M) hR (moduleSheaf_isFiniteLocallyConstant (s := s) M)) := by
  intro a
  obtain ⟨c, rfl⟩ := classOf_surjective (FiberAutGroup s) M a
  exact ⟨Quotient.mk _ (cocycleSheafTorsor s M c), representedTorsorClass_cocycle s M hR c⟩

/-- The actual torsor-class/common-continuous-H¹ bijection for finite modules.
Its forward function is the explicit representative/cocycle extraction above;
no additive structure is imposed by transport through this equivalence. -/
def moduleTorsorClassEquiv : TorsorClass (moduleSheaf s M) ≃ H1 (FiberAutGroup s) M :=
  Equiv.ofBijective
    (torsorClassToH1 s (moduleScheme s M) (moduleFiberMulEquiv s M)
      (moduleFiber_action s M) hR (moduleSheaf_isFiniteLocallyConstant (s := s) M))
    ⟨torsorClassToH1_injective s (moduleScheme s M) (moduleFiberMulEquiv s M)
      (moduleFiber_action s M) hR (moduleSheaf_isFiniteLocallyConstant (s := s) M),
      moduleTorsorClassToH1_surjective s M hR⟩

/-- The quotient equivalence retains the actual representative evaluation formula. -/
@[simp] theorem moduleTorsorClassEquiv_mk (P : Torsor (moduleSheaf s M)) :
    moduleTorsorClassEquiv s M hR (Quotient.mk _ P) =
      representedTorsorClass s (moduleScheme s M) (moduleFiberMulEquiv s M)
        (moduleFiber_action s M) hR (moduleSheaf_isFiniteLocallyConstant (s := s) M) P := rfl

/-- The constructed affine inverse has the prescribed common cohomology class. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem moduleTorsorClassEquiv_cocycle (c : Cocycle (FiberAutGroup s) M) :
    moduleTorsorClassEquiv s M hR (Quotient.mk _ (cocycleSheafTorsor s M c)) =
      classOf (FiberAutGroup s) M c := representedTorsorClass_cocycle s M hR c

/-- An explicit formula for the inverse equivalence on every cocycle class. -/
theorem moduleTorsorClassEquiv_symm_classOf (c : Cocycle (FiberAutGroup s) M) :
    (moduleTorsorClassEquiv s M hR).symm (classOf (FiberAutGroup s) M c) =
      Quotient.mk _ (cocycleSheafTorsor s M c) := by
  apply (moduleTorsorClassEquiv s M hR).injective
  rw [Equiv.apply_symm_apply, moduleTorsorClassEquiv_cocycle]

end ModuleSurjectivity
end AlgebraicGeometry.Scheme.EtaleH1.SchemeTorsorClassification

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3515a724d1456b378cc48ef63d9500fa9a3231b02ee0cfd21b087ab1536944eb.
Definitions, hypotheses and universes are retained modulo native names. -/
