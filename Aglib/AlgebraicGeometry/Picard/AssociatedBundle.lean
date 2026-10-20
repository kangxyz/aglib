/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitInverse

public import Aglib.AlgebraicGeometry.Picard.FrameTorsor
public import Aglib.AlgebraicGeometry.Picard.UnitDescent
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorPullback
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.AssociatedBundle` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`07bf568a4aa094f8a6d493d503fed718fbb8b5ed6fb1d4e95a9e51d25286a9f7`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle LineBundleClass )
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Associated line bundles of actual etale multiplicative torsors

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For an arbitrary scheme X and a genuine small-etale torsor under the
represented coefficient sheaf Gm, construct a covering family indexed by
all actual sections on all etale test schemes. Its covering property is
proved from the torsor's covering-sieve local nonemptiness. Unique transport
produces literal global units on actual pairwise fiber products; its identity,
restriction, and transitivity laws give an actual UnitDescent.Cocycle.
The fixed native rank-one descent construction then produces an actual
locally rank-one structure-module sheaf and its actual O-linear charts.

The convention is positive: if p_j = u_ij * p_i, the corresponding chart
on j is the chart on i followed by multiplication by u_ij. Sending each
section to its own descended chart constructs an equivariant sheaf map;
the proved same-coefficient torsor-map theorem makes this an actual sheaf
isomorphism. Recovery of an existing line bundle is proved by constructing
an isomorphism of its native chosen-overlap descent data with these unit
transitions, and applying full faithfulness of the same stack equivalence.

The sole retained general theorem family is exactly
EtaleDescent.EtaleLineBundleDescent: the stack property for the fixed
pseudofunctor of actual locally rank-one module sheaves and native module
pullback, for Scheme.etaleTopology. Its source boundary, Stacks Tags 023T
and 05B2 and actual rank-one preservation/descent, is documented in
EtaleDescent. No separate Picard/H1 classification, arbitrary gluing datum,
or final comparison equivalence is a premise. No curve, properness,
characteristic, or integer-level hypothesis is needed here. This module
asserts no additive compatibility with tensor products or contracted sums.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite Limits Bicategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle
open EtaleDescent UnitDescent
open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients
universe u
variable {X : Scheme.{u}}

section Cover
variable {A : AbelianSheaf.{u, u + 1} X} (P : Torsor A)

/-- Every section on every etale test scheme indexes a genuine trivialization. -/
def Index := Σ U : X.Etale, P.carrier.obj.obj (op U)
/-- The etale test scheme underlying a torsor-section index. -/
def coverObject (i : Index P) : Scheme.{u} := i.1.left
/-- The structure map of the etale scheme indexing a torsor section. -/
def coverMap (i : Index P) : coverObject P i ⟶ X := i.1.hom
instance coverMap_etale (i : Index P) : Etale (coverMap P i) := i.1.prop

theorem cover_mem : Sieve.ofArrows (coverObject P) (coverMap P) ∈ Scheme.etaleTopology X := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨?_, fun i => i.1.prop⟩
  intro x
  have h := P.locally_nonempty (etaleTerminal X)
  change _ ∈ X.smallGrothendieckTopology @Etale (etaleTerminal X) at h
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at h
  obtain ⟨V, f, v, ⟨p⟩, _, hv⟩ := h x
  refine ⟨⟨V, p⟩, v, ?_⟩
  have hf : f.left = V.hom := by simpa using (MorphismProperty.Over.w f)
  change f.left v = x at hv
  rw [hf] at hv
  exact hv

end Cover

variable (P : Torsor (gm X))

/-- The unique positive scalar carrying one torsor section to another. -/
def transport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : (gm X).obj.obj U :=
  (P.sectionEquiv U s).symm t

@[simp] theorem action_transport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    P.action U (transport P U s t) s = t := (P.sectionEquiv U s).apply_symm_apply t

theorem transport_eq (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U)
    (a : (gm X).obj.obj U) (ha : P.action U a s = t) : transport P U s t = a := by
  apply (P.sectionEquiv U s).injective
  exact (action_transport P U s t).trans ha.symm

@[simp] theorem transport_self (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    transport P U s s = 0 := transport_eq P U s s 0 (P.zero_action U s)

theorem transport_trans (U : X.Etaleᵒᵖ) (s t r : P.carrier.obj.obj U) :
    transport P U s t + transport P U t r = transport P U s r := by
  symm
  apply transport_eq
  rw [add_comm, P.add_action, action_transport, action_transport]

theorem transport_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    (gm X).obj.map f (transport P U s t) =
      transport P V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  symm
  apply transport_eq
  rw [← P.naturality, action_transport]

/-- Literal invertible global regular function of positive transport. -/
def transportUnit (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : Γ(U.unop.left, ⊤)ˣ :=
  (unitsSections X U (transport P U s t)).toMul

@[simp] theorem transportUnit_self (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    transportUnit P U s s = 1 := by simp [transportUnit]

theorem transportUnit_trans (U : X.Etaleᵒᵖ) (s t r : P.carrier.obj.obj U) :
    transportUnit P U s t * transportUnit P U t r = transportUnit P U s r := by
  exact congrArg Additive.toMul ((unitsSections X U).map_add _ _).symm |>.trans
    (congrArg (fun a => (unitsSections X U a).toMul) (transport_trans P U s t r))

theorem transportUnit_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    pullUnit f.unop.left (transportUnit P U s t) =
      transportUnit P V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  unfold pullUnit transportUnit
  rw [← unitsSections_naturality, transport_naturality]

/-- A fixed genuine scheme fiber product. -/
def chosenPullback {A B S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) : ChosenPullback f g where
  pullback := CategoryTheory.Limits.pullback f g
  p₁ := pullback.fst f g
  p₂ := pullback.snd f g
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback f g).isLimit

/-- The chosen pairwise fibre product of two torsor trivialization schemes. -/
def overlap (i j : Index P) : ChosenPullback (coverMap P i) (coverMap P j) :=
  chosenPullback _ _

instance overlap_p₁_etale (i j : Index P) : Etale (overlap P i j).p₁ := by
  dsimp [overlap, chosenPullback]
  infer_instance
instance overlap_p₂_etale (i j : Index P) : Etale (overlap P i j).p₂ := by
  dsimp [overlap, chosenPullback]
  infer_instance
instance overlap_p_etale (i j : Index P) : Etale (overlap P i j).p := by
  dsimp [overlap, chosenPullback]
  infer_instance

/-- The pairwise overlap viewed as an object of the small etale site of `X`. -/
def overlapEtale (i j : Index P) : X.Etale := Scheme.Etale.mk (overlap P i j).p

/-- The first projection from the overlap in the small etale site. -/
def overlapFst (i j : Index P) : overlapEtale P i j ⟶ i.1 :=
  MorphismProperty.Over.homMk (overlap P i j).p₁ (by simp [overlapEtale, coverMap]) (by trivial)
/-- The second projection from the overlap in the small etale site. -/
def overlapSnd (i j : Index P) : overlapEtale P i j ⟶ j.1 :=
  MorphismProperty.Over.homMk (overlap P i j).p₂ (by simp [overlapEtale, coverMap]) (by trivial)


/-- The chosen triple overlap of three torsor trivialization schemes, with its pairwise
projections. -/
def triple (i j k : Index P) : ChosenPullback₃ (overlap P i j) (overlap P j k) (overlap P i k) where
  chosenPullback := chosenPullback (overlap P i j).p₂ (overlap P j k).p₁
  l := Classical.choice (ChosenPullback.LiftStruct.nonempty (by
    simp only [Category.assoc]
    rw [(overlap P i j).condition, ← Category.assoc,
      (chosenPullback (overlap P i j).p₂ (overlap P j k).p₁).condition,
      Category.assoc, (overlap P j k).condition]) (by simp))

instance triple_p_etale (i j k : Index P) : Etale (triple P i j k).p := by
  dsimp [triple, chosenPullback]
  infer_instance

/-- The triple overlap viewed as an object of the small etale site of `X`. -/
def tripleEtale (i j k : Index P) : X.Etale := Scheme.Etale.mk (triple P i j k).p

/-- The first projection from the triple overlap to a trivialization scheme. -/
def tripleFst (i j k : Index P) : tripleEtale P i j k ⟶ i.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₁ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The middle projection from the triple overlap to a trivialization scheme. -/
def tripleMid (i j k : Index P) : tripleEtale P i j k ⟶ j.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₂ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The third projection from the triple overlap to a trivialization scheme. -/
def tripleSnd (i j k : Index P) : tripleEtale P i j k ⟶ k.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₃ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The projection from the triple overlap to the first and second pairwise overlap. -/
def triple12 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P i j :=
  MorphismProperty.Over.homMk (triple P i j k).p₁₂ (by simp [tripleEtale, overlapEtale]) (by
      trivial)
/-- The projection from the triple overlap to the second and third pairwise overlap. -/
def triple23 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P j k :=
  MorphismProperty.Over.homMk (triple P i j k).p₂₃ (by simp [tripleEtale, overlapEtale]) (by
      trivial)
/-- The projection from the triple overlap to the first and third pairwise overlap. -/
def triple13 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P i k :=
  MorphismProperty.Over.homMk (triple P i j k).p₁₃ (by simp [tripleEtale, overlapEtale]) (by
      trivial)

@[simp] theorem triple12_fst (i j k : Index P) :
    triple12 P i j k ≫ overlapFst P i j = tripleFst P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₂_p₁
@[simp] theorem triple12_snd (i j k : Index P) :
    triple12 P i j k ≫ overlapSnd P i j = tripleMid P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₂_p₂
@[simp] theorem triple23_fst (i j k : Index P) :
    triple23 P i j k ≫ overlapFst P j k = tripleMid P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₂₃_p₂
@[simp] theorem triple23_snd (i j k : Index P) :
    triple23 P i j k ≫ overlapSnd P j k = tripleSnd P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₂₃_p₃
@[simp] theorem triple13_fst (i j k : Index P) :
    triple13 P i j k ≫ overlapFst P i k = tripleFst P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₃_p₁
@[simp] theorem triple13_snd (i j k : Index P) :
    triple13 P i j k ≫ overlapSnd P i k = tripleSnd P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₃_p₃

/-- The diagonal from a trivialization scheme to its self-overlap in the small etale site. -/
def diagonalEtale (i : Index P) : i.1 ⟶ overlapEtale P i i :=
  MorphismProperty.Over.homMk (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal
      (overlap P) i)
    (by
      change AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal (overlap P) i ≫
          (overlap P i i).p = i.1.hom
      rw [← (overlap P i i).hp₁, ← Category.assoc,
          AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal_p₁, Category.id_comp]
      rfl) (by trivial)
@[simp] theorem diagonal_fst (i : Index P) :
    diagonalEtale P i ≫ overlapFst P i i = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  exact AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal_p₁ (overlap P) i
@[simp] theorem diagonal_snd (i : Index P) :
    diagonalEtale P i ≫ overlapSnd P i i = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  exact AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal_p₂ (overlap P) i

/-- The global unit carrying the first restricted torsor section to the second on their overlap. -/
def overlapUnit (i j : Index P) : Γ((overlap P i j).pullback, ⊤)ˣ :=
  transportUnit P (op (overlapEtale P i j))
    (P.carrier.obj.map (overlapFst P i j).op i.2)
    (P.carrier.obj.map (overlapSnd P i j).op j.2)

/-- Literal global-unit transitions obtained from the original torsor action. -/
def cocycle : AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle (overlap P)
    (triple P) where
  unit := overlapUnit P
  diagonal i := by
    change pullUnit (diagonalEtale P i).left (transportUnit P _ _ _) = 1
    erw [transportUnit_naturality P (diagonalEtale P i).op]
    simp only [← Functor.map_comp_apply, ← op_comp, diagonal_fst, diagonal_snd,
      op_id, transportUnit_self]
  cocycle i j k := by
    change pullUnit (triple12 P i j k).left (transportUnit P _ _ _) *
      pullUnit (triple23 P i j k).left (transportUnit P _ _ _) =
      pullUnit (triple13 P i j k).left (transportUnit P _ _ _)
    erw [transportUnit_naturality P (triple12 P i j k).op,
      transportUnit_naturality P (triple23 P i j k).op,
      transportUnit_naturality P (triple13 P i j k).op]
    simp only [← Functor.map_comp_apply, ← op_comp, triple12_fst, triple12_snd,
      triple23_fst, triple23_snd, triple13_fst, triple13_snd]
    exact transportUnit_trans P _ _ _ _

/-- Any common etale refinement has its canonical map into the overlap. -/
def overlapLift {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    V ⟶ overlapEtale P i j :=
  MorphismProperty.Over.homMk
    ((overlap P i j).isPullback.lift a.left b.left
      (by exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))
    (by
      change (overlap P i j).isPullback.lift _ _ _ ≫ (overlap P i j).p = V.hom
      rw [← (overlap P i j).hp₁, ← Category.assoc, IsPullback.lift_fst]
      exact MorphismProperty.Over.w a) (by trivial)

@[simp] theorem overlapLift_fst {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) : overlapLift P i j a b ≫ overlapFst P i j = a := by
  apply MorphismProperty.Over.Hom.ext
  exact IsPullback.lift_fst _ _ _ _
@[simp] theorem overlapLift_snd {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) : overlapLift P i j a b ≫ overlapSnd P i j = b := by
  apply MorphismProperty.Over.Hom.ext
  exact IsPullback.lift_snd _ _ _ _

/-- The chosen-overlap transition has the literal unique-transport value on every refinement. -/
theorem overlapUnit_pullback {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) :
    pullUnit (overlapLift P i j a b).left (overlapUnit P i j) =
      transportUnit P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) := by
  have hh := transportUnit_naturality P (overlapLift P i j a b).op
    (P.carrier.obj.map (overlapFst P i j).op i.2)
    (P.carrier.obj.map (overlapSnd P i j).op j.2)
  change pullUnit (overlapLift P i j a b).left (overlapUnit P i j) = _ at hh
  simpa only [← Functor.map_comp_apply, ← op_comp, overlapLift_fst, overlapLift_snd] using hh

/-- All refinement maps of the native descent datum have the same positive transport. -/
theorem descentData_hom {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) :
    (cocycle P).descentData.descentData.hom V.hom a.left b.left
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) =
    AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left b.left
      (transportUnit P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2)) := by
  change Pseudofunctor.DescentData'.pullHom' (cocycle P).descentData.hom
    V.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) = _
  have h₁ : (overlapLift P i j a b).left ≫ (overlap P i j).p₁ = a.left :=
    IsPullback.lift_fst _ _ _ _
  have h₂ : (overlapLift P i j a b).left ≫ (overlap P i j).p₂ = b.left :=
    IsPullback.lift_snd _ _ _ _
  rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ (overlapLift P i j a b).left
    (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) h₁ h₂]
  change Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition (overlap P i j).p₁
        (overlap P i j).p₂ (overlapUnit P i j))
      (overlapLift P i j a b).left a.left b.left h₁ h₂ = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.pullHom_transition]
  have hh := congrArg Units.val (overlapUnit_pullback P i j a b)
  exact congrArg (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left
      b.left) hh

open Pseudofunctor.LocallyDiscreteOpToCat

private theorem presheafHom_map_eq_pullHom {S : Scheme.{u}}
    {M N : lineBundles.obj (.mk (op S))} {U V : S.Etale} (f : V ⟶ U)
    (g : (lineBundles.map U.hom.op.toLoc).toFunctor.obj M ⟶
      (lineBundles.map U.hom.op.toLoc).toFunctor.obj N) :
    (lineBundles.presheafHom M N).map ((Scheme.Etale.forget S).map f).op g =
      pullHom g f.left V.hom V.hom
        (MorphismProperty.Over.w f) (MorphismProperty.Over.w f) := rfl

/-- The unit-line comparison between pullback of the unit object and the unit object on the
source. -/
def unitIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (lineBundles.map f.op.toLoc).toFunctor.obj (unitObject Z) ≅ unitObject Y :=
  ObjectProperty.isoMk _ (pullbackUnitIso f)

/-- The line-bundle pullback comparison from a composite morphism to iterated pullback. -/
def compIso {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ f = q) (M : lineBundles.obj (.mk (op S))) :
    (lineBundles.map q.op.toLoc).toFunctor.obj M ≅
      (lineBundles.map a.op.toLoc).toFunctor.obj ((lineBundles.map f.op.toLoc).toFunctor.obj M) :=
  (Cat.Hom.toNatIso (lineBundles.mapComp' f.op.toLoc a.op.toLoc q.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, w]))).app M

theorem unitIso_comp {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ f = q) :
    (compIso f a q w (unitObject S)).hom ≫
      (lineBundles.map a.op.toLoc).toFunctor.map (unitIso f).hom ≫ (unitIso a).hom =
        (unitIso q).hom := by
  subst q
  apply ObjectProperty.hom_ext
  exact Scheme.Modules.pullbackUnitIso_comp_inv a f

/-- Multiplication by the global section `a` on the unit line bundle. -/
def unitScalar (Y : Scheme.{u}) (a : Γ(Y, ⊤)) : unitObject Y ⟶ unitObject Y :=
  ObjectProperty.homMk (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap
      Y (SheafOfModules.unit Y.ringCatSheaf) a)

theorem transition_eq {Y₁ Y₂ Z : Scheme.{u}} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (u : Γ(Z, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a b u = (unitIso a).hom
        ≫ unitScalar Z u ≫ (unitIso b).inv := rfl

@[reassoc] theorem rawRestriction_unit {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y)
    (q : Z ⟶ S) (w : a ≫ f = q) (M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f.op.toLoc).toFunctor.obj M ⟶ unitObject Y) :
    pullHom (α ≫ (unitIso f).inv) a q q w w ≫ (unitIso q).hom =
      (compIso f a q w M).hom ≫ (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        (unitIso a).hom := by
  have hh : (lineBundles.map a.op.toLoc).toFunctor.map (unitIso f).inv ≫
      (compIso f a q w (unitObject S)).inv ≫ (unitIso q).hom = (unitIso a).hom := by
    rw [← unitIso_comp f a q w]
    simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  change ((compIso f a q w M).hom ≫
    (lineBundles.map a.op.toLoc).toFunctor.map (α ≫ (unitIso f).inv) ≫
      (compIso f a q w (unitObject S)).inv) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [hh]

/-- Native descent compatibility is exactly positive scalar compatibility of frames. -/
theorem chart_comm_to_raw {Y₁ Y₂ Z S : Scheme.{u}}
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (q : Z ⟶ S)
    (ha : a ≫ f₁ = q) (hb : b ≫ f₂ = q)
    (M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f₁.op.toLoc).toFunctor.obj M ⟶ unitObject Y₁)
    (β : (lineBundles.map f₂.op.toLoc).toFunctor.obj M ⟶ unitObject Y₂)
    (u : Γ(Z, ⊤))
    (hc : (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a b u =
      (compIso f₁ a q ha M).inv ≫ (compIso f₂ b q hb M).hom ≫
        (lineBundles.map b.op.toLoc).toFunctor.map β) :
    pullHom (α ≫ (unitIso f₁).inv) a q q ha ha ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition q q u =
      pullHom (β ≫ (unitIso f₂).inv) b q q hb hb := by
  apply (cancel_mono (unitIso q).hom).mp
  rw [transition_eq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rawRestriction_unit_assoc, rawRestriction_unit]
  have hh := congrArg (fun k => (compIso f₁ a q ha M).hom ≫ k ≫ (unitIso b).hom) hc
  simpa only [transition_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hh

/-- Positive compatibility of raw frames implies the native descent square. -/
theorem raw_to_chart_comm {Y₁ Y₂ Z S : Scheme.{u}}
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (q : Z ⟶ S)
    (ha : a ≫ f₁ = q) (hb : b ≫ f₂ = q)
    (M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f₁.op.toLoc).toFunctor.obj M ⟶ unitObject Y₁)
    (β : (lineBundles.map f₂.op.toLoc).toFunctor.obj M ⟶ unitObject Y₂)
    (u : Γ(Z, ⊤))
    (hr : pullHom (α ≫ (unitIso f₁).inv) a q q ha ha ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition q q u =
      pullHom (β ≫ (unitIso f₂).inv) b q q hb hb) :
    (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a b u =
      (compIso f₁ a q ha M).inv ≫ (compIso f₂ b q hb M).hom ≫
        (lineBundles.map b.op.toLoc).toFunctor.map β := by
  apply (cancel_epi (compIso f₁ a q ha M).hom).mp
  apply (cancel_mono (unitIso b).hom).mp
  have hh := congrArg (fun k => k ≫ (unitIso q).hom) hr
  rw [transition_eq] at hh
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [rawRestriction_unit_assoc, rawRestriction_unit] at hh
  simpa only [transition_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hh


/-- Recovery is compatible with every native refinement, with the coherence displayed. -/
theorem recovery_square {ι : Type*} {S : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ S} {sq : ∀ i j, ChosenPullback (f i) (f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (c : AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle sq sq₃) (h :
        EtaleLineBundleDescent.{u})
    (hf : Sieve.ofArrows U f ∈ Scheme.etaleTopology S)
    (i j : ι) {V : Scheme.{u}} (q : V ⟶ S) (a : V ⟶ U i) (b : V ⟶ U j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (lineBundles.map a.op.toLoc).toFunctor.map ((c.recoveryIso h hf).hom.hom i) ≫
      c.descentData.descentData.hom q a b ha hb =
    (compIso (f i) a q ha (c.descendedObject h hf)).inv ≫
      (compIso (f j) b q hb (c.descendedObject h hf)).hom ≫
      (lineBundles.map b.op.toLoc).toFunctor.map ((c.recoveryIso h hf).hom.hom j) := by
  simpa only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    compIso, Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv,
    Category.assoc] using (c.recoveryIso h hf).hom.comm q a b ha hb

variable (h : EtaleLineBundleDescent.{u})
/-- The actual locally rank-one O_X-module descended from torsor transport. -/
def lineBundle : LineBundle X := (cocycle P).descended h (cover_mem P)

/-- The actual local trivialization specified by each original torsor section. -/
def chart (i : Index P) :
    (Scheme.Modules.pullback (coverMap P i)).obj (lineBundle P h).val ≅
      SheafOfModules.unit (coverObject P i).ringCatSheaf :=
  (cocycle P).chart h (cover_mem P) i

/-- The descent recovery map before identifying the pulled structure module. -/
def chartMap (i : Index P) :
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj ((cocycle P).descendedObject h
        (cover_mem P)) ⟶
      unitObject (coverObject P i) :=
  ((cocycle P).recoveryIso h (cover_mem P)).hom.hom i

/-- The descended local chart valued in the pulled-back base unit object,
using the supplied etale line-bundle descent input. -/
def rawChart (i : Index P) :
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj ((cocycle P).descendedObject h
        (cover_mem P)) ⟶
      (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj (unitObject X) :=
  chartMap P h i ≫ (unitIso (coverMap P i)).inv

/-- Exact positive transition law for the actual local frames on arbitrary refinements. -/
theorem rawChart_relation {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    pullHom (rawChart P h i) a.left V.hom V.hom
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w a) ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition V.hom V.hom
        ((transportUnit P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) :
            Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
    pullHom (rawChart P h j) b.left V.hom V.hom
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w b) := by
  apply chart_comm_to_raw (coverMap P i) (coverMap P j) a.left b.left V.hom
    (MorphismProperty.Over.w a) (MorphismProperty.Over.w b)
    ((cocycle P).descendedObject h (cover_mem P)) (chartMap P h i) (chartMap P h j)
  have hh := recovery_square (cocycle P) h (cover_mem P) i j
    V.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b)
  rw [descentData_hom P i j a b] at hh
  exact hh

open FrameTorsor

@[simp] theorem site_id_left (U : X.Etale) : (𝟙 U : U ⟶ U).left = 𝟙 U.left := rfl

/-- The original torsor section is sent to its own actual descended chart. -/
def toFrame (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    (frameSheaf h X (lineBundle P h)).obj.obj U :=
  (frameSectionsEquiv h X (lineBundle P h) U).symm (chart P h ⟨U.unop, s⟩)

@[simp] theorem toFrame_raw (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    frameRawHom h X (lineBundle P h) U (toFrame P h U s) = rawChart P h ⟨U.unop, s⟩ := by
  rfl

set_option maxHeartbeats 1600000 in
-- Retain the original source budget: descended-chart conversion measured 1016766 heartbeats.
theorem toFrame_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : P.carrier.obj.obj U) :
    (frameSheaf h X (lineBundle P h)).obj.map f (toFrame P h U s) =
      toFrame P h V (P.carrier.obj.map f s) := by
  apply frameRawHom_injective h X (lineBundle P h) V
  rw [frameRawHom_naturality, toFrame_raw, toFrame_raw]
  change pullHom (F := lineBundles)
    (M₁ := (cocycle P).descendedObject h (cover_mem P)) (M₂ := unitObject X) (rawChart P h
        ⟨U.unop, s⟩) f.unop.left V.unop.hom V.unop.hom
    (MorphismProperty.Over.w f.unop) (MorphismProperty.Over.w f.unop) =
      rawChart P h ⟨V.unop, P.carrier.obj.map f s⟩
  have hh := rawChart_relation P h ⟨U.unop, s⟩ ⟨V.unop, P.carrier.obj.map f s⟩
    f.unop (𝟙 V.unop)
  simp only [site_id_left] at hh
  simp only [Quiver.Hom.op_unop, op_id, op_unop, CategoryTheory.Functor.map_id,
    types_id_apply, transportUnit_self, Units.val_one,
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition_self_one] at hh
  apply ObjectProperty.hom_ext
  have hh' := congrArg (fun k => k.hom) hh
  change (pullHom (F := lineBundles)
    (M₁ := (cocycle P).descendedObject h (cover_mem P)) (M₂ := unitObject X) (rawChart P h
        ⟨U.unop, s⟩) f.unop.left V.unop.hom V.unop.hom
    (MorphismProperty.Over.w f.unop) (MorphismProperty.Over.w f.unop)).hom ≫ 𝟙 _ =
      (pullHom (F := lineBundles)
    (M₁ := (cocycle P).descendedObject h (cover_mem P)) (M₂ := unitObject X) (rawChart P h
        ⟨V.unop, P.carrier.obj.map f s⟩) (𝟙 V.unop.left)
        V.unop.hom V.unop.hom (Category.id_comp _) (Category.id_comp _)).hom at hh'
  rw [CategoryTheory.Category.comp_id] at hh'
  have hid := congrArg (fun k => k.hom)
    (pullHom_id (F := lineBundles)
    (M₁ := (cocycle P).descendedObject h (cover_mem P)) (M₂ := unitObject X) (rawChart P h
        ⟨V.unop, P.carrier.obj.map f s⟩))
  exact hh'.trans hid


theorem toFrame_equivariant (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U) (s : P.carrier.obj.obj U) :
    toFrame P h U (P.action U a s) = frameAction h X (lineBundle P h) U a (toFrame P h U s) := by
  apply frameRawHom_injective h X (lineBundle P h) U
  rw [frameRawHom_action, toFrame_raw, toFrame_raw]
  have hh := rawChart_relation P h ⟨U.unop, s⟩ ⟨U.unop, P.action U a s⟩
    (𝟙 U.unop) (𝟙 U.unop)
  have ht : transportUnit P U s (P.action U a s) = (unitsSections X U a).toMul := by
    unfold transportUnit
    rw [transport_eq P U s (P.action U a s) a rfl]
  simp only [site_id_left] at hh
  simp only [op_id, op_unop, CategoryTheory.Functor.map_id, types_id_apply] at hh
  erw [pullHom_id, pullHom_id, ht] at hh
  exact hh.symm

/-- An actual equivariant morphism of sheaves, constructed without torsor classification. -/
def frameMap : Scheme.EtaleH1.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X
    (lineBundle P h)) where
  map := ⟨{ app U := ↾(toFrame P h U)
            naturality {U V} f := by
              ext s
              exact (toFrame_naturality P h f s).symm }⟩
  equivariant := toFrame_equivariant P h

/-- The genuine frame torsor of the associated bundle recovers the original torsor. -/
def frameIso : Scheme.EtaleH1.Torsor.Iso P (frameTorsor h X
    (lineBundle P h)) := (frameMap P h).toIso


/-- The torsor recovery isomorphism sends a section to its literal descended local chart. -/
@[simp] theorem frameIso_sections (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    frameSectionsEquiv h X (lineBundle P h) U
      ((frameIso P h).carrierIso.hom.hom.app U s) = chart P h ⟨U.unop, s⟩ :=
  (frameSectionsEquiv h X (lineBundle P h) U).apply_symm_apply _

/-- A literal frame, regarded in the fixed full rank-one subcategory. -/
def frameChart (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    (lineBundles.map U.unop.hom.op.toLoc).toFunctor.obj (ofLineBundle X L) ≅
      unitObject U.unop.left :=
  ObjectProperty.isoMk _ (frameSectionsEquiv h X L U s)

theorem frameChart_raw (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    (frameChart h L U s).hom ≫ (unitIso U.unop.hom).inv = frameRawHom h X L U s := by
  apply ObjectProperty.hom_ext
  change (frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom) ≫
    (pullbackUnitIso U.unop.hom).inv = frameHom h X L U s
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A genuine equivariant map gives exactly the required chart square on every etale refinement. -/
theorem frameMap_chart_comm (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X L))
    {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    (lineBundles.map a.left.op.toLoc).toFunctor.map
      (frameChart h L (op i.1) (r.map.hom.app (op i.1) i.2)).hom ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left b.left
          ((transportUnit P (op V) (P.carrier.obj.map a.op i.2)
            (P.carrier.obj.map b.op j.2) : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
      (compIso (coverMap P i) a.left V.hom (MorphismProperty.Over.w a) (ofLineBundle X L)).inv ≫
      (compIso (coverMap P j) b.left V.hom (MorphismProperty.Over.w b) (ofLineBundle X L)).hom ≫
      (lineBundles.map b.left.op.toLoc).toFunctor.map
        (frameChart h L (op j.1) (r.map.hom.app (op j.1) j.2)).hom := by
  apply raw_to_chart_comm (coverMap P i) (coverMap P j) a.left b.left V.hom
    (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) (ofLineBundle X L)
    (frameChart h L (op i.1) (r.map.hom.app (op i.1) i.2)).hom
    (frameChart h L (op j.1) (r.map.hom.app (op j.1) j.2)).hom
  erw [frameChart_raw h L (op i.1) (r.map.hom.app (op i.1) i.2),
    frameChart_raw h L (op j.1) (r.map.hom.app (op j.1) j.2)]
  have h₁ := congrArg (fun k => k i.2) (r.map.hom.naturality a.op)
  have h₂ := congrArg (fun k => k j.2) (r.map.hom.naturality b.op)
  change r.map.hom.app (op V) (P.carrier.obj.map a.op i.2) =
    (frameSheaf h X L).obj.map a.op (r.map.hom.app (op i.1) i.2) at h₁
  change r.map.hom.app (op V) (P.carrier.obj.map b.op j.2) =
    (frameSheaf h X L).obj.map b.op (r.map.hom.app (op j.1) j.2) at h₂
  have hr := r.equivariant (op V)
    (transport P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2))
    (P.carrier.obj.map a.op i.2)
  change r.map.hom.app (op V) (P.action (op V) _ _) =
    frameAction h X L (op V) _ (r.map.hom.app (op V) _) at hr
  rw [action_transport, h₁, h₂] at hr
  have hh := congrArg (frameRawHom h X L (op V)) hr.symm
  rw [frameRawHom_action, frameRawHom_naturality, frameRawHom_naturality,
    presheafHom_map_eq_pullHom, presheafHom_map_eq_pullHom] at hh
  exact hh

/-- Isomorphism of actual native overlap descent data supplied by an equivariant frame map. -/
def frameMapChosenDescentIso (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X L)) :
    Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L)) ≅
        (cocycle P).descentData :=
  Pseudofunctor.DescentData'.isoMk
    (fun i => frameChart h L (op i.1) (r.map.hom.app (op i.1) i.2)) (by
      intro i j
      exact frameMap_chart_comm P h L r i j (overlapFst P i j) (overlapSnd P i j))

/-- Effective and fully faithful native descent recovers the actual bundle underlying a frame map.
-/
def lineBundleIsoOfFrameMap (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X L)) :
        (lineBundle P h).val ≅ L.val := by
  let e := Pseudofunctor.DescentData'.descentDataEquivalence lineBundles (overlap P) (triple P)
  let d : (lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L) ≅
      (cocycle P).descentData.descentData :=
    (e.counitIso.app _).symm ≪≫ e.functor.mapIso (frameMapChosenDescentIso P h L r)
  let t := AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence h
      (cover_mem P)
  let z := t.fullyFaithfulFunctor.preimageIso (((cocycle P).recoveryIso h (cover_mem P)) ≪≫ d.symm)
  exact (rankOne.prop (.mk (op X))).fullyFaithfulι.isoEquiv z

/-- Rebuilding from the genuine frame torsor recovers each actual line bundle. -/
def bundleRecovery (L : LineBundle X) :
    (lineBundle (frameTorsor h X L) h).val ≅ L.val :=
  lineBundleIsoOfFrameMap (frameTorsor h X L) h L
    { map := 𝟙 _
      equivariant := fun _ _ _ => rfl }

/-- Pullback of a global module map is compatible with the native pseudofunctor coherence. -/
theorem pullHom_global {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ f = q) {M N : lineBundles.obj (.mk (op S))} (g : M ⟶ N) :
    pullHom ((lineBundles.map f.op.toLoc).toFunctor.map g) a q q w w =
      (lineBundles.map q.op.toLoc).toFunctor.map g := by
  have hn := (Cat.Hom.toNatIso
    (lineBundles.mapComp' f.op.toLoc a.op.toLoc q.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, w]))).hom.naturality g
  change (lineBundles.map q.op.toLoc).toFunctor.map g ≫ (compIso f a q w N).hom =
    (compIso f a q w M).hom ≫
      (lineBundles.map a.op.toLoc).toFunctor.map ((lineBundles.map f.op.toLoc).toFunctor.map g)
          at hn
  change (compIso f a q w M).hom ≫
    (lineBundles.map a.op.toLoc).toFunctor.map ((lineBundles.map f.op.toLoc).toFunctor.map g) ≫
    (compIso f a q w N).inv = _
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Transport of a frame from `L` to `M` by precomposition with the inverse line-bundle
isomorphism. -/
def mapFrame {L M : LineBundle X} (e : L.val ≅ M.val) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) : (frameSheaf h X M).obj.obj U :=
  (frameSectionsEquiv h X M U).symm
    ((Scheme.Modules.pullback U.unop.hom).mapIso e.symm ≪≫ frameSectionsEquiv h X L U s)

/-- The inverse of the line-bundle isomorphism `e`, viewed as a morphism in the line-bundle
category. -/
def bundleIsoHom {L M : LineBundle X} (e : L.val ≅ M.val) : ofLineBundle X M ⟶ ofLineBundle X L :=
  ObjectProperty.homMk e.inv

theorem mapFrame_raw {L M : LineBundle X} (e : L.val ≅ M.val) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    frameRawHom h X M U (mapFrame h e U s) =
      (lineBundles.map U.unop.hom.op.toLoc).toFunctor.map (bundleIsoHom e) ≫ frameRawHom h X L
          U s := by
  apply ObjectProperty.hom_ext
  change ((Scheme.Modules.pullback U.unop.hom).map e.inv ≫
    (frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom)) ≫
      (pullbackUnitIso U.unop.hom).inv =
        (Scheme.Modules.pullback U.unop.hom).map e.inv ≫ frameHom h X L U s
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem mapFrame_naturality {L M : LineBundle X} (e : L.val ≅ M.val)
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : (frameSheaf h X L).obj.obj U) :
    (frameSheaf h X M).obj.map f (mapFrame h e U s) =
      mapFrame h e V ((frameSheaf h X L).obj.map f s) := by
  apply frameRawHom_injective h X M V
  rw [frameRawHom_naturality, mapFrame_raw, mapFrame_raw, frameRawHom_naturality]
  have hc := homRestriction_comp (ofLineBundle X M) (ofLineBundle X L)
    (ofLineBundle X (unitBundle X)) ((Scheme.Etale.forget X).map f.unop).op
    ((lineBundles.map U.unop.hom.op.toLoc).toFunctor.map (bundleIsoHom e))
    (frameRawHom h X L U s)
  rw [hc]
  apply congrArg (fun k => k ≫
    (lineBundles.presheafHom (ofLineBundle X L) (ofLineBundle X (unitBundle X))).map
      ((Scheme.Etale.forget X).map f.unop).op (frameRawHom h X L U s))
  rw [presheafHom_map_eq_pullHom]
  exact pullHom_global U.unop.hom f.unop.left V.unop.hom (MorphismProperty.Over.w f.unop)
      (bundleIsoHom e)

theorem mapFrame_equivariant {L M : LineBundle X} (e : L.val ≅ M.val)
    (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U) (s : (frameSheaf h X L).obj.obj U) :
    mapFrame h e U (frameAction h X L U a s) = frameAction h X M U a (mapFrame h e U s) := by
  apply frameRawHom_injective h X M U
  rw [mapFrame_raw, frameRawHom_action, frameRawHom_action, mapFrame_raw]
  exact (Category.assoc _ _ _).symm

/-- An actual O_X-linear isomorphism gives an actual equivariant frame-sheaf isomorphism. -/
def frameIsoOfBundleIso {L M : LineBundle X} (e : L.val ≅ M.val) :
    Scheme.EtaleH1.Torsor.Iso (frameTorsor h X L) (frameTorsor h X M) :=
  (show Scheme.EtaleH1.Torsor.Hom (𝟙 (gm X)) (frameTorsor h X L)
      (frameTorsor h X M) from
    { map := ⟨{ app U := ↾(mapFrame h e U)
                naturality {U V} f := by
                  ext s
                  exact (mapFrame_naturality h e f s).symm }⟩
      equivariant := mapFrame_equivariant h e }).toIso

/-- Equivariantly isomorphic torsors have actually isomorphic associated module sheaves. -/
def bundleIsoOfTorsorIso {Q : Torsor (gm X)} (e :
    Scheme.EtaleH1.Torsor.Iso P Q) :
    (lineBundle P h).val ≅ (lineBundle Q h).val :=
  lineBundleIsoOfFrameMap P h (lineBundle Q h)
    { map := (e.trans (frameIso Q h)).carrierIso.hom
      equivariant := (e.trans (frameIso Q h)).equivariant }

/-- The associated actual line bundle on isomorphism classes. -/
def torsorClassToBundle : TorsorClass (gm X) → LineBundleClass X :=
  Quotient.map (fun P => lineBundle P h)
    (fun _ _ ⟨e⟩ => ⟨bundleIsoOfTorsorIso _ h e⟩)

/-- The actual frame torsor on isomorphism classes. -/
def bundleClassToTorsor : LineBundleClass X → TorsorClass (gm X) :=
  Quotient.map (frameTorsor h X) (fun _ _ ⟨e⟩ => ⟨frameIsoOfBundleIso h e⟩)

/-- The proved correspondence of actual line-bundle and genuine Gm-torsor isomorphism classes.
No tensor/contracted-sum additivity assertion is made here. -/
def classEquiv : LineBundleClass X ≃ TorsorClass (gm X) where
  toFun := bundleClassToTorsor h
  invFun := torsorClassToBundle h
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro L
    exact Quotient.sound ⟨bundleRecovery h L⟩
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro P
    exact Quotient.sound ⟨(frameIso P h).symm⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle
