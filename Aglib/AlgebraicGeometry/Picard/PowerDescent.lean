/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.AssociatedBundle
public import Aglib.AlgebraicGeometry.Picard.TrivializedPowerTorsor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.PowerDescent` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`a8c6de7efdd99ce980db7aec0046e34e9fc5a2819ed28522557b422658402f22`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle tensorPowerLineBundle)
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
# Descent of actual root torsors to power-trivialized line bundles

Manuscript: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Lean: `4.34.1`; mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The input is an actual small-etale mu_n torsor on an arbitrary scheme.
Unique positive transport on the coefficient-generic all-section cover
produces actual root-valued transitions, whose inclusions are literal units.
The units satisfy the native cocycle and have nth power one. They descend
through the fixed rank-one module stack to an actual line bundle with charts.
Canonical tensor-power pullback and fully faithful stack descent glue their
actual normalized powers to a specified global trivialization. The displayed
chart-power equality is proved. These constructions need no positivity or
invertibility assumption on the level.

For positive n globally invertible on X, sending each original torsor section
to its own positive compatible chart constructs an actual natural equivariant
sheaf map. The same-coefficient torsor-map theorem supplies actual recovery.
For an original pair, reciprocal recovery is an actual module isomorphism
whose nth tensor power preserves that pair's specified trivialization.
The module makes no additive, quotient-group, or H1-classification assertion.

The only retained general theorem is EtaleDescent.EtaleLineBundleDescent,
the fixed actual native rank-one stack boundary (Stacks Tags 023T/05B2).
No local-root theorem, classification, or application-specific gluing result
is assumed. The positive frame convention is phi : L -> O and phi^n = tau.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite Limits Bicategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent
open EtaleDescent UnitDescent AssociatedBundle
open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients
universe u
variable {X : Scheme.{u}} {n : ℕ} (P : Torsor (mu X n))
/-- The unique positive scalar carrying one torsor section to another. -/
def transport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : (mu X n).obj.obj U :=
  (P.sectionEquiv U s).symm t

@[simp] theorem action_transport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    P.action U (transport P U s t) s = t := (P.sectionEquiv U s).apply_symm_apply t

theorem transport_eq (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U)
    (a : (mu X n).obj.obj U) (ha : P.action U a s = t) : transport P U s t = a := by
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
    (mu X n).obj.map f (transport P U s t) =
      transport P V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  symm
  apply transport_eq
  rw [← P.naturality, action_transport]

/-- Literal root of unity carrying one section to another. -/
def transportRoot (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    rootsOfUnity n Γ(U.unop.left, ⊤) :=
  (rootsSections X n U (transport P U s t)).toMul

/-- Literal unit obtained by the actual root inclusion. -/
def transportUnit (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : Γ(U.unop.left, ⊤)ˣ :=
  (unitsSections X U ((inclusion X n).hom.app U (transport P U s t))).toMul

@[simp] theorem transportUnit_root (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    transportUnit P U s t = (transportRoot P U s t).val :=
  inclusion_apply X n U _

-- Keep the unit power rule; exposing the opaque root coordinate alone does not prove the power
-- law.
@[nolint simpNF, simp] theorem transportUnit_pow (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    transportUnit P U s t ^ n = 1 := by
  rw [transportUnit_root]
  exact (transportRoot P U s t).property

-- Keep diagonal unit normalization; transportUnit_root only exposes an opaque root coordinate.
@[nolint simpNF, simp] theorem transportUnit_self (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    transportUnit P U s s = 1 := by simp [transportUnit]

theorem transportUnit_trans (U : X.Etaleᵒᵖ) (s t r : P.carrier.obj.obj U) :
    transportUnit P U s t * transportUnit P U t r = transportUnit P U s r := by
  have ht := congrArg (fun a => (unitsSections X U ((inclusion X n).hom.app U a)).toMul)
    (transport_trans P U s t r)
  simpa only [transportUnit, map_add, toMul_add] using ht

theorem transportUnit_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    pullUnit f.unop.left (transportUnit P U s t) =
      transportUnit P V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  unfold pullUnit transportUnit
  rw [← unitsSections_naturality, ← inclusion_naturality, transport_naturality]

/-- The chosen fibre product of the two specified torsor-cover maps. -/
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

/-- The chosen double overlap as an object of the small etale site. -/
def overlapEtale (i j : Index P) : X.Etale := Scheme.Etale.mk (overlap P i j).p

/-- The first projection from the double overlap in the small etale site. -/
def overlapFst (i j : Index P) : overlapEtale P i j ⟶ i.1 :=
  MorphismProperty.Over.homMk (overlap P i j).p₁ (by simp [overlapEtale, coverMap]) (by trivial)
/-- The second projection from the double overlap in the small etale site. -/
def overlapSnd (i j : Index P) : overlapEtale P i j ⟶ j.1 :=
  MorphismProperty.Over.homMk (overlap P i j).p₂ (by simp [overlapEtale, coverMap]) (by trivial)


/-- The chosen triple overlap with its compatible projections to all three double overlaps. -/
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

/-- The chosen triple overlap as an object of the small etale site. -/
def tripleEtale (i j k : Index P) : X.Etale := Scheme.Etale.mk (triple P i j k).p

/-- The projection from the triple overlap to the first cover object. -/
def tripleFst (i j k : Index P) : tripleEtale P i j k ⟶ i.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₁ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The projection from the triple overlap to the middle cover object. -/
def tripleMid (i j k : Index P) : tripleEtale P i j k ⟶ j.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₂ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The projection from the triple overlap to the last cover object. -/
def tripleSnd (i j k : Index P) : tripleEtale P i j k ⟶ k.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₃ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The projection from the triple overlap to the overlap of its first two cover objects. -/
def triple12 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P i j :=
  MorphismProperty.Over.homMk (triple P i j k).p₁₂ (by simp [tripleEtale, overlapEtale]) (by
      trivial)
/-- The projection from the triple overlap to the overlap of its last two cover objects. -/
def triple23 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P j k :=
  MorphismProperty.Over.homMk (triple P i j k).p₂₃ (by simp [tripleEtale, overlapEtale]) (by
      trivial)
/-- The projection from the triple overlap to the overlap of its first and last cover objects. -/
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

/-- The diagonal map from a cover object to its chosen self-overlap in the small etale site. -/
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

/-- The global transition unit carrying the first specified local torsor section to the
second on their chosen overlap. -/
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

/-- The local frame of the object descended using the supplied line-bundle stack input,
expressed in the native pullback-module coordinates. -/
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
-- Retain the original source budget: descended-chart conversion measured 1013327 heartbeats.
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


theorem toFrame_equivariant (U : X.Etaleᵒᵖ) (a : (mu X n).obj.obj U) (s : P.carrier.obj.obj U) :
    toFrame P h U (P.action U a s) = frameAction h X (lineBundle P h) U ((inclusion X
        n).hom.app U a) (toFrame P h U s) := by
  apply frameRawHom_injective h X (lineBundle P h) U
  rw [frameRawHom_action, toFrame_raw, toFrame_raw]
  have hh := rawChart_relation P h ⟨U.unop, s⟩ ⟨U.unop, P.action U a s⟩
    (𝟙 U.unop) (𝟙 U.unop)
  have ht : transportUnit P U s (P.action U a s) = (unitsSections X U ((inclusion X n).hom.app
      U a)).toMul := by
    unfold transportUnit
    rw [transport_eq P U s (P.action U a s) a rfl]
  simp only [site_id_left] at hh
  simp only [op_id, op_unop, CategoryTheory.Functor.map_id, types_id_apply] at hh
  erw [pullHom_id, pullHom_id, ht] at hh
  exact hh.symm

/-- The positive chart map is equivariant for the actual root inclusion. -/
def frameMap : Scheme.EtaleH1.Torsor.Hom (inclusion X n) P
    (frameTorsor h X (lineBundle P h)) where
  map := ⟨{ app U := ↾(toFrame P h U)
            naturality {U V} f := by
              ext s
              exact (toFrame_naturality P h f s).symm }⟩
  equivariant := toFrame_equivariant P h

open TrivializedPower UnitPower PowerPullback TrivializedPowerTorsor

/-- The normalized actual tensor power of an arbitrary positive frame. -/
def normalizedPower {Y : Scheme.{u}} {L : LineBundle Y}
    (φ : L.val ≅ SheafOfModules.unit Y.ringCatSheaf) (k : ℕ) :
    (tensorPowerLineBundle Y L k).val ≅ SheafOfModules.unit Y.ringCatSheaf :=
  powerIso Y (M := unitLineBundle Y) φ k ≪≫ unitPowerIso Y k

/-- Pullback of a normalized frame power is its normalized pulled-back power. -/
theorem normalizedPower_pullback {Y Z : Scheme.{u}} (f : Z ⟶ Y) {L : LineBundle Y}
    (φ : L.val ≅ SheafOfModules.unit Y.ringCatSheaf) (k : ℕ) :
    (pullbackPowerIso f L k).hom ≫
      (normalizedPower (L := pullbackLineBundle f L)
        ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f) k).hom =
    (Scheme.Modules.pullback f).map (normalizedPower φ k).hom ≫ (pullbackUnitIso f).hom := by
  let Q : Pair Y k := ⟨L, normalizedPower φ k⟩
  have hp : powerValue Y Q φ = 1 :=
    (powerValue_eq_one_iff Y Q φ).mpr rfl
  have hq := powerValue_pullback f Q φ
  rw [hp, map_one] at hq
  have hc := (powerValue_eq_one_iff Z (pullbackPair f Q)
    ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f)).mp hq
  change (normalizedPower (L := pullbackLineBundle f L)
    ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f) k).hom =
      (pullbackPowerIso f L k).inv ≫
        (Scheme.Modules.pullback f).map (normalizedPower φ k).hom ≫ (pullbackUnitIso f).hom at hc
  rw [hc, Iso.hom_inv_id_assoc]

/-- A local frame of L gives a literal local frame of the actual global L^k. -/
def powerFrame {Y : Scheme.{u}} (L : LineBundle X) (p : Y ⟶ X)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) (k : ℕ) :
    (Scheme.Modules.pullback p).obj (tensorPowerLineBundle X L k).val ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  pullbackPowerIso p L k ≪≫ normalizedPower (L := pullbackLineBundle p L) φ k

/-- The arbitrary-line-bundle frame-power square for actual native restrictions. -/
theorem powerFrame_nativePullFrame {Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) (k : ℕ) :
    nativePullFrame (tensorPowerLineBundle X L k) p q f w (powerFrame L p φ k) =
      powerFrame L q (nativePullFrame L p q f w φ) k := by
  subst q
  unfold nativePullFrame
  change Iso.refl _ ≪≫ (((Scheme.Modules.pullbackComp f p).app
    (tensorPowerLineBundle X L k).val).symm ≪≫
      ((Scheme.Modules.pullback f).mapIso (powerFrame L p φ k) ≪≫ pullbackUnitIso f)) =
    powerFrame L (f ≫ p) (Iso.refl _ ≪≫
      (((Scheme.Modules.pullbackComp f p).app L.val).symm ≪≫
        ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f))) k
  rw [Iso.refl_trans, Iso.refl_trans]
  apply Iso.ext
  unfold powerFrame normalizedPower
  have htrans := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans Z
    (L := pullbackLineBundle (f ≫ p) L)
    (M := pullbackLineBundle f (pullbackLineBundle p L)) (N := unitLineBundle Z)
    ((Scheme.Modules.pullbackComp f p).app L.val).symm
    ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f) k
  rw [htrans]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hp := normalizedPower_pullback f (L := pullbackLineBundle p L) φ k
  change (pullbackPowerIso f (pullbackLineBundle p L) k).hom ≫
    (powerIso Z (M := unitLineBundle Z)
      ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f) k).hom ≫
        (unitPowerIso Z k).hom =
    (Scheme.Modules.pullback f).map
      ((powerIso Y (M := unitLineBundle Y) φ k).hom ≫ (unitPowerIso Y k).hom) ≫
        (pullbackUnitIso f).hom at hp
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hp
  rw [← hp]
  have hc :=
      AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullbackNaturality.pullbackPowerIso_comp
      f p L k
  simpa only [Category.assoc, Iso.app_inv] using congrArg (fun a => a ≫
    (powerIso Z (M := unitLineBundle Z)
      ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f) k).hom ≫
        (unitPowerIso Z k).hom) hc

/-- Root-valued positive scalar postcomposition disappears under the normalized power. -/
theorem normalizedPower_root {Y : Scheme.{u}} {L : LineBundle Y}
    (φ : L.val ≅ SheafOfModules.unit Y.ringCatSheaf) (a : Γ(Y, ⊤)ˣ)
    (ha : a ^ n = 1) :
    normalizedPower (φ ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Y _ a) n =
        normalizedPower φ n := by
  let Q : Pair Y n := ⟨L, normalizedPower φ n⟩
  have hp : powerValue Y Q φ = 1 := (powerValue_eq_one_iff Y Q φ).mpr rfl
  have hs : powerValue Y Q (φ ≪≫
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Y _ a) = 1 := by
    rw [powerValue_scalar, hp, ha, mul_one]
  exact Iso.ext ((powerValue_eq_one_iff Y Q _).mp hs)


/-- The frame-section coordinate of each descended chart is literal. -/
@[simp] theorem toFrame_sections (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    frameSectionsEquiv h X (lineBundle P h) U (toFrame P h U s) =
      chart P h ⟨U.unop, s⟩ := (frameSectionsEquiv h X (lineBundle P h) U).apply_symm_apply _

/-- Descended charts follow the actual native pullback comparison. -/
theorem chart_restriction {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : P.carrier.obj.obj U) :
    nativePullFrame (lineBundle P h) U.unop.hom V.unop.hom f.unop.left f.unop.w
      (chart P h ⟨U.unop, s⟩) = chart P h ⟨V.unop, P.carrier.obj.map f s⟩ := by
  have hh := frameSections_restriction h X (lineBundle P h) f (toFrame P h U s)
  rw [toFrame_naturality, toFrame_sections, toFrame_sections] at hh
  exact Iso.ext hh.symm

/-- The positive root action is the literal scalar action on the descended charts. -/
theorem chart_action (U : X.Etaleᵒᵖ) (a : (mu X n).obj.obj U) (s : P.carrier.obj.obj U) :
    chart P h ⟨U.unop, P.action U a s⟩ = chart P h ⟨U.unop, s⟩ ≪≫
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso U.unop.left _
        ((rootsSections X n U a).toMul : Γ(U.unop.left, ⊤)ˣ) := by
  have hh := congrArg (frameSectionsEquiv h X (lineBundle P h) U)
    (toFrame_equivariant P h U a s)
  rw [toFrame_sections,
      AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameAction_sections,
      toFrame_sections, inclusion_apply] at hh
  exact hh

/-- The prescribed local trivializations of the actual tensor power. -/
def powerChart (i : Index P) :
    (Scheme.Modules.pullback (coverMap P i)).obj (tensorPowerLineBundle X (lineBundle P h) n).val ≅
      SheafOfModules.unit (coverObject P i).ringCatSheaf :=
  powerFrame (lineBundle P h) (coverMap P i) (chart P h i) n

theorem powerChart_restriction {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : P.carrier.obj.obj U) :
    nativePullFrame (tensorPowerLineBundle X (lineBundle P h) n)
      U.unop.hom V.unop.hom f.unop.left f.unop.w
        (powerChart P h ⟨U.unop, s⟩) = powerChart P h ⟨V.unop, P.carrier.obj.map f s⟩ := by
  unfold powerChart
  erw [powerFrame_nativePullFrame, chart_restriction]
  rfl

theorem powerChart_independent (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    powerChart P h ⟨U.unop, s⟩ = powerChart P h ⟨U.unop, t⟩ := by
  have hc := chart_action P h U (transport P U s t) s
  rw [action_transport] at hc
  change pullbackPowerIso U.unop.hom (lineBundle P h) n ≪≫
      normalizedPower (L := pullbackLineBundle U.unop.hom (lineBundle P h)) (chart P h ⟨U.unop,
          s⟩) n =
    pullbackPowerIso U.unop.hom (lineBundle P h) n ≪≫
      normalizedPower (L := pullbackLineBundle U.unop.hom (lineBundle P h)) (chart P h ⟨U.unop,
          t⟩) n
  rw [hc]
  exact congrArg (fun e => pullbackPowerIso U.unop.hom (lineBundle P h) n ≪≫ e)
    (normalizedPower_root (L := pullbackLineBundle U.unop.hom (lineBundle P h))
      (chart P h ⟨U.unop, s⟩) (transportRoot P U s t).val
      (transportRoot P U s t).property).symm

/-- Raw chart restriction and native frame restriction are the same module morphism. -/
theorem rawFrameRestriction {Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (pullHom (ObjectProperty.homMk (φ.hom ≫ (pullbackUnitIso p).inv) :
      (lineBundles.map p.op.toLoc).toFunctor.obj (ofLineBundle X L) ⟶
      (lineBundles.map p.op.toLoc).toFunctor.obj (unitObject X)) f q q w w).hom =
      (nativePullFrame L p q f w φ).hom ≫ (pullbackUnitIso q).inv := by
  apply (cancel_mono (pullbackUnitIso q).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pullHom_frame_hom]
  dsimp only [ObjectProperty.homMk]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Conjugation of an abstract isomorphism square, with no native pullback reduction. -/
theorem isoSquare {C : Type*} [Category C] {A B D E F G : C}
    (c₁ : A ≅ B) (c₂ : A ≅ D) (d₁ : E ≅ F) (d₂ : E ≅ G)
    (α : B ⟶ F) (β : D ⟶ G)
    (hr : c₁.hom ≫ α ≫ d₁.inv = c₂.hom ≫ β ≫ d₂.inv) :
    α ≫ d₁.inv ≫ d₂.hom = c₁.inv ≫ c₂.hom ≫ β := by
  apply (cancel_epi c₁.hom).mp
  apply (cancel_mono d₂.inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hr

/-- Opaque native restriction formula, using exactly the displayed coherence isomorphisms. -/
theorem pullHom_compIso {Y Z S : Scheme.{u}} (p : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ p = q) (L M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map p.op.toLoc).toFunctor.obj L ⟶
      (lineBundles.map p.op.toLoc).toFunctor.obj M) :
    pullHom α a q q w w = (compIso p a q w L).hom ≫
      (lineBundles.map a.op.toLoc).toFunctor.map α ≫ (compIso p a q w M).inv := by
  simp only [pullHom, compIso, Iso.app_hom, Iso.app_inv,
    Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv]

/-- Equality of native restrictions is exactly the descent square for two global objects. -/
theorem rawSquare_to_descent {Y₁ Y₂ Z S : Scheme.{u}}
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (q : Z ⟶ S)
    (ha : a ≫ f₁ = q) (hb : b ≫ f₂ = q)
    (L M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f₁.op.toLoc).toFunctor.obj L ⟶
      (lineBundles.map f₁.op.toLoc).toFunctor.obj M)
    (β : (lineBundles.map f₂.op.toLoc).toFunctor.obj L ⟶
      (lineBundles.map f₂.op.toLoc).toFunctor.obj M)
    (hr : pullHom α a q q ha ha = pullHom β b q q hb hb) :
    (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        (compIso f₁ a q ha M).inv ≫ (compIso f₂ b q hb M).hom =
      (compIso f₁ a q ha L).inv ≫ (compIso f₂ b q hb L).hom ≫
        (lineBundles.map b.op.toLoc).toFunctor.map β := by
  exact isoSquare (C := lineBundles.obj (.mk (op Z)))
    (compIso f₁ a q ha L) (compIso f₂ b q hb L)
    (compIso f₁ a q ha M) (compIso f₂ b q hb M)
    ((lineBundles.map a.op.toLoc).toFunctor.map α)
    ((lineBundles.map b.op.toLoc).toFunctor.map β)
    ((pullHom_compIso f₁ a q ha L M α).symm.trans
      (hr.trans (pullHom_compIso f₂ b q hb L M β)))

section Gluing
variable (L M : lineBundles.obj (.mk (op X)))
    (e : ∀ i : Index P, (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj L ≅
      (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj M)
    (he : ∀ i j : Index P,
      pullHom (e i).hom (overlap P i j).p₁ (overlap P i j).p (overlap P i j).p
        (by simp) (by simp) =
      pullHom (e j).hom (overlap P i j).p₂ (overlap P i j).p (overlap P i j).p
        (by simp) (by simp))

/-- Compatible local isomorphisms give an isomorphism on native chosen overlaps. -/
def glueChosenIso :
    Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj L) ≅
    Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj M) :=
  Pseudofunctor.DescentData'.isoMk (F := lineBundles)
    (D₁ := Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj L))
    (D₂ := Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj M)) e (by
      intro i j
      have hc := rawSquare_to_descent (coverMap P i) (coverMap P j)
        (overlap P i j).p₁ (overlap P i j).p₂ (overlap P i j).p
        (by simp) (by simp) L M (e i).hom (e j).hom (he i j)
      simpa only [Pseudofunctor.DescentData'.ofDescentData_hom,
        Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
        compIso, Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv,
        Category.assoc] using hc)


/-- The same isomorphism on all native refinements. -/
def glueDescentIso :
    (lineBundles.toDescentData (coverMap P)).obj L ≅
      (lineBundles.toDescentData (coverMap P)).obj M :=
  let E := Pseudofunctor.DescentData'.descentDataEquivalence lineBundles (overlap P) (triple P)
  (E.counitIso.app _).symm ≪≫ E.functor.mapIso (glueChosenIso P L M e he) ≪≫ E.counitIso.app _

/-- Fully faithful stack descent glues the specified actual local isomorphisms. -/
def glueIso : L ≅ M :=
  (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence h
      (cover_mem P)).fullyFaithfulFunctor.preimageIso
    (glueDescentIso P L M e he)

/-- Gluing recovers each specified actual local isomorphism. -/
theorem glueIso_hom (i : Index P) :
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.map (glueIso P h L M e he).hom =
      (e i).hom := by
  have hh := (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence
      h (cover_mem P)).fullyFaithfulFunctor.map_preimage
    (glueDescentIso P L M e he).hom
  have hh' := congrArg (fun k => k.hom i) hh
  change (lineBundles.map (coverMap P i).op.toLoc).toFunctor.map
    (glueIso P h L M e he).hom = 𝟙 _ ≫ (e i).hom ≫ 𝟙 _ at hh'
  simpa only [Category.id_comp, Category.comp_id] using hh'
end Gluing


/-- Power charts before identifying the native pullback of O. -/
def powerChartRaw (i : Index P) :
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj
      (ofLineBundle X (tensorPowerLineBundle X (lineBundle P h) n)) ≅
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj (unitObject X) :=
  ObjectProperty.isoMk _ (powerChart P h i ≪≫ (pullbackUnitIso (coverMap P i)).symm)

theorem powerChartRaw_compatible (i j : Index P) :
    pullHom (powerChartRaw P h i).hom (overlap P i j).p₁ (overlap P i j).p (overlap P i j).p
      (by simp) (by simp) =
    pullHom (powerChartRaw P h j).hom (overlap P i j).p₂ (overlap P i j).p (overlap P i j).p
      (by simp) (by simp) := by
  apply ObjectProperty.hom_ext
  have h₁ := rawFrameRestriction (tensorPowerLineBundle X (lineBundle P h) n)
    (coverMap P i) (overlap P i j).p (overlap P i j).p₁ (by simp) (powerChart P h i)
  have h₂ := rawFrameRestriction (tensorPowerLineBundle X (lineBundle P h) n)
    (coverMap P j) (overlap P i j).p (overlap P i j).p₂ (by simp) (powerChart P h j)
  have hr₁ := powerChart_restriction P h (overlapFst P i j).op i.2
  have hr₂ := powerChart_restriction P h (overlapSnd P i j).op j.2
  have he := hr₁.trans ((powerChart_independent P h (op (overlapEtale P i j))
    (P.carrier.obj.map (overlapFst P i j).op i.2) (P.carrier.obj.map (overlapSnd P i j).op
        j.2)).trans hr₂.symm)
  have he' := congrArg
    (fun e : (Scheme.Modules.pullback (overlap P i j).p).obj
        (tensorPowerLineBundle X (lineBundle P h) n).val ≅
          SheafOfModules.unit (overlap P i j).pullback.ringCatSheaf =>
      e.hom ≫ (pullbackUnitIso (overlap P i j).p).inv) he
  exact h₁.trans (he'.trans h₂.symm)

/-- The actual global power trivialization glued from the prescribed chart powers. -/
def trivialization : (tensorPowerLineBundle X (lineBundle P h) n).val ≅
    SheafOfModules.unit X.ringCatSheaf :=
  (rankOne.prop (.mk (op X))).fullyFaithfulι.isoEquiv
    (glueIso P h (ofLineBundle X (tensorPowerLineBundle X (lineBundle P h) n))
      (unitObject X) (powerChartRaw P h) (powerChartRaw_compatible P h))

/-- The global trivialization recovers exactly the actual normalized chart powers. -/
theorem trivialization_chart (i : Index P) :
    (Scheme.Modules.pullback (coverMap P i)).map (trivialization P h).hom ≫
      (pullbackUnitIso (coverMap P i)).hom = (powerChart P h i).hom := by
  have hh := congrArg (fun v => v.hom)
    (glueIso_hom P h (ofLineBundle X (tensorPowerLineBundle X (lineBundle P h) n))
      (unitObject X) (powerChartRaw P h) (powerChartRaw_compatible P h) i)
  change (Scheme.Modules.pullback (coverMap P i)).map (trivialization P h).hom =
    (powerChart P h i).hom ≫ (pullbackUnitIso (coverMap P i)).inv at hh
  rw [hh, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual pair descended from an actual root torsor. -/
def pair : Pair X n := ⟨lineBundle P h, trivialization P h⟩

/-- Each original torsor section gives a literal positive compatible frame. -/
theorem chart_compatible (i : Index P) :
    (normalizedPower (L := pullbackLineBundle (coverMap P i) (lineBundle P h)) (chart P h i)
        n).hom =
      (pullbackPair (coverMap P i) (pair P h)).trivialization.hom := by
  change _ = (pullbackPowerIso (coverMap P i) (lineBundle P h) n).inv ≫
    (Scheme.Modules.pullback (coverMap P i)).map (trivialization P h).hom ≫
      (pullbackUnitIso (coverMap P i)).hom
  rw [trivialization_chart]
  change _ = (pullbackPowerIso (coverMap P i) (lineBundle P h) n).inv ≫
    (pullbackPowerIso (coverMap P i) (lineBundle P h) n).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

variable (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Sending each root-torsor section to its descended chart is a genuine torsor map. -/
def torsorMap : Scheme.EtaleH1.Torsor.Hom (𝟙 (mu X n)) P (torsor h X n
    hn hinv (pair P h)) where
  map := ⟨{
    app U := ↾(fun s => ⟨toFrame P h U s, by
      apply (framePowerSection_eq_zero_iff h X (pair P h) U _).mpr
      erw [toFrame_sections]
      exact chart_compatible P h ⟨U.unop, s⟩⟩)
    naturality {U V} f := by
      ext s
      apply Subtype.ext
      exact (toFrame_naturality P h f s).symm }⟩
  equivariant U a s := by
    apply Subtype.ext
    exact toFrame_equivariant P h U a s

/-- Actual equivariant recovery, proved by the same-coefficient torsor-map theorem. -/
def torsorRecovery : Scheme.EtaleH1.Torsor.Iso P (torsor h X n hn hinv
    (pair P h)) :=
  (torsorMap P h hn hinv).toIso

/-- Recovery sends an actual section to its own prescribed positive compatible chart. -/
@[simp] theorem torsorRecovery_sections (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    (sectionsEquiv h X n hn hinv (pair P h) U
      ((torsorRecovery P h hn hinv).carrierIso.hom.hom.app U s)).val =
      chart P h ⟨U.unop, s⟩ := toFrame_sections P h U s


/-- A genuine equivariant map gives exactly the required chart square on every etale refinement. -/
theorem frameMap_chart_comm (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (inclusion X n) P (frameTorsor h X L))
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
    (r : Scheme.EtaleH1.Torsor.Hom (inclusion X n) P (frameTorsor h X L)) :
    Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L)) ≅
        (cocycle P).descentData :=
  Pseudofunctor.DescentData'.isoMk
    (fun i => frameChart h L (op i.1) (r.map.hom.app (op i.1) i.2)) (by
      intro i j
      exact frameMap_chart_comm P h L r i j (overlapFst P i j) (overlapSnd P i j))

/-- The frame map identifies the full native descent data. -/
def frameMapDescentIso (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (inclusion X n) P (frameTorsor h X L)) :
    (lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L) ≅
      (cocycle P).descentData.descentData :=
  let E := Pseudofunctor.DescentData'.descentDataEquivalence lineBundles (overlap P) (triple P)
  (E.counitIso.app _).symm ≪≫ E.functor.mapIso (frameMapChosenDescentIso P h L r)

/-- Effective and fully faithful native descent recovers the bundle of a root-equivariant frame
map. -/
def lineBundleIsoOfFrameMap (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (inclusion X n) P (frameTorsor h X
        L)) : (lineBundle P h).val ≅ L.val :=
  (rankOne.prop (.mk (op X))).fullyFaithfulι.isoEquiv
    ((AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence h
        (cover_mem P)).fullyFaithfulFunctor.preimageIso
      ((cocycle P).recoveryIso h (cover_mem P) ≪≫ (frameMapDescentIso P h L r).symm))

/-- The bundle recovery carries exactly the original positive charts. -/
theorem lineBundleIsoOfFrameMap_chart (L : LineBundle X)
    (r : Scheme.EtaleH1.Torsor.Hom (inclusion X n) P (frameTorsor h X
        L)) (i : Index P) :
    (Scheme.Modules.pullback (coverMap P i)).map (lineBundleIsoOfFrameMap P h L r).hom ≫
      (frameSectionsEquiv h X L (op i.1) (r.map.hom.app (op i.1) i.2)).hom =
        (chart P h i).hom := by
  have hh := (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence
      h (cover_mem P)).fullyFaithfulFunctor.map_preimage
    ((cocycle P).recoveryIso h (cover_mem P) ≪≫ (frameMapDescentIso P h L r).symm).hom
  have hh' := congrArg (fun k => (k.hom i).hom) hh
  change (Scheme.Modules.pullback (coverMap P i)).map (lineBundleIsoOfFrameMap P h L r).hom = _
      at hh'
  rw [hh']
  change ((chart P h i).hom ≫
    ((frameSectionsEquiv h X L (op i.1) (r.map.hom.app (op i.1) i.2)).inv ≫ 𝟙 _)) ≫
      (frameSectionsEquiv h X L (op i.1) (r.map.hom.app (op i.1) i.2)).hom = _
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Forgetting compatibility is the actual map into the underlying frame torsor. -/
def forgetCompatible (Q : Pair X n) :
    Scheme.EtaleH1.Torsor.Hom (inclusion X n) (torsor h X n hn hinv Q)
        (frameTorsor h X Q.lineBundle) where
  map := ⟨{ app U := ↾Subtype.val
            naturality := by intros; rfl }⟩
  equivariant _ _ _ := rfl

/-- The reciprocal recovery is an actual isomorphism of module sheaves. -/
def pairBundleRecovery (Q : Pair X n) :
    (pair (torsor h X n hn hinv Q) h).lineBundle.val ≅ Q.lineBundle.val :=
  lineBundleIsoOfFrameMap (torsor h X n hn hinv Q) h Q.lineBundle (forgetCompatible h hn hinv Q)

/-- Tensor-power frame formation is natural in an actual bundle isomorphism. -/
theorem powerFrame_map {Y : Scheme.{u}} {L M : LineBundle X}
    (e : L.val ≅ M.val) (p : Y ⟶ X)
    (φ : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf) (k : ℕ) :
    (Scheme.Modules.pullback p).map (powerIso X e k).hom ≫ (powerFrame M p φ k).hom =
      (powerFrame L p ((Scheme.Modules.pullback p).mapIso e ≪≫ φ) k).hom := by
  have hh := congrArg Iso.hom
      (PowerPullbackNaturality.pullbackPowerIso_naturality p e k)
  unfold powerFrame normalizedPower
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans Y (L :=
      pullbackLineBundle p L)
    (M := pullbackLineBundle p M) (N := unitLineBundle Y) ((Scheme.Modules.pullback p).mapIso
        e) φ k]
  simp only [Iso.trans_hom, Category.assoc]
  change (Scheme.Modules.pullback p).map (powerIso X e k).hom ≫ (pullbackPowerIso p M k).hom =
    (pullbackPowerIso p L k).hom ≫ (powerIso Y ((Scheme.Modules.pullback p).mapIso e) k).hom at hh
  rw [← Category.assoc, ← Category.assoc, hh]
  simp only [Category.assoc]

include h in
/-- Equality of actual module maps is detected on the genuine torsor cover. -/
theorem moduleHom_ext (L M : LineBundle X) (a b : L.val ⟶ M.val)
    (hab : ∀ i : Index P, (Scheme.Modules.pullback (coverMap P i)).map a =
      (Scheme.Modules.pullback (coverMap P i)).map b) : a = b := by
  have hh : (ObjectProperty.homMk a : ofLineBundle X L ⟶ ofLineBundle X M) =
      ObjectProperty.homMk b := by
    apply (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence h
        (cover_mem P)).fullyFaithfulFunctor.map_injective
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    apply ObjectProperty.hom_ext
    exact hab i
  exact congrArg (fun z => z.hom) hh

/-- Reciprocal recovery preserves the specified trivialization, not just the line bundle. -/
theorem pairBundleRecovery_compatible (Q : Pair X n) :
    (powerIso X (pairBundleRecovery h hn hinv Q) n).hom ≫ Q.trivialization.hom =
      (pair (torsor h X n hn hinv Q) h).trivialization.hom := by
  let R := torsor h X n hn hinv Q
  let e := pairBundleRecovery h hn hinv Q
  apply moduleHom_ext R h (tensorPowerLineBundle X (lineBundle R h) n) (unitLineBundle X)
  intro i
  apply (cancel_mono (pullbackUnitIso (coverMap R i)).hom).mp
  rw [Functor.map_comp, Category.assoc]
  change (Scheme.Modules.pullback (coverMap R i)).map (powerIso X e n).hom ≫
    (Scheme.Modules.pullback (coverMap R i)).map Q.trivialization.hom ≫
      (pullbackUnitIso (coverMap R i)).hom =
    (Scheme.Modules.pullback (coverMap R i)).map (trivialization R h).hom ≫
      (pullbackUnitIso (coverMap R i)).hom
  rw [trivialization_chart]
  let φ := frameSectionsEquiv h X Q.lineBundle (op i.1) i.2.val
  have hφ := (framePowerSection_eq_zero_iff h X Q (op i.1) i.2.val).mp i.2.property
  have ht : (Scheme.Modules.pullback (coverMap R i)).map Q.trivialization.hom ≫
      (pullbackUnitIso (coverMap R i)).hom = (powerFrame Q.lineBundle (coverMap R i) φ n).hom := by
    change (normalizedPower (L := pullbackLineBundle (coverMap R i) Q.lineBundle) φ n).hom =
      (pullbackPowerIso (coverMap R i) Q.lineBundle n).inv ≫
        (Scheme.Modules.pullback (coverMap R i)).map Q.trivialization.hom ≫
          (pullbackUnitIso (coverMap R i)).hom at hφ
    unfold powerFrame
    rw [Iso.trans_hom, hφ, Iso.hom_inv_id_assoc]
  rw [ht, powerFrame_map (L := lineBundle R h) (M := Q.lineBundle) e (coverMap R i) φ n]
  have he : (Scheme.Modules.pullback (coverMap R i)).mapIso e ≪≫ φ = chart R h i := by
    apply Iso.ext
    exact lineBundleIsoOfFrameMap_chart R h Q.lineBundle (forgetCompatible h hn hinv Q) i
  rw [he]
  rfl

/-- The inverse construction recovers each original actual power-trivialized pair. -/
theorem pairRecovery (Q : Pair X n) :
    AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.Isomorphic X (pair (torsor h X
        n hn hinv Q) h) Q :=
  ⟨pairBundleRecovery h hn hinv Q, pairBundleRecovery_compatible h hn hinv Q⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent
