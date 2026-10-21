/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.HenselianResidue
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ResidueLift
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# Finite etale residue equivalence over a Henselian local ring

Finite continuous actions represent the finite set of functions between two
geometric fibres. Henselian lifting of residue sections then lifts morphisms
between the original finite etale covers. The forward functor is the literal
residue base change, without completeness or Noetherian assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.HenselianEquivalence

universe u v w

section FiniteActions

variable {C : Type v} [Category.{w} C] (H : C ⥤ FintypeCat.{u})

/-- Conjugation on all functions between two finite fibres. -/
private def functionAction (X Y : C) : Action FintypeCat.{u} (Aut H) where
  V := FintypeCat.of (H.obj X → H.obj Y)
  ρ :=
    { toFun := fun g => FintypeCat.homMk (fun f x => g.hom.app Y (f (g.inv.app X x)))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

private theorem functionAction_continuous (X Y : C) :
    (functionAction H X Y).IsContinuous := by
  rw [Action.isContinuous_def]
  let : TopologicalSpace (H.obj X → H.obj Y) := ⊥
  let V := FintypeCat.of (H.obj X → H.obj Y)
  have : DiscreteTopology V := ⟨rfl⟩
  let c : Aut H × V → Aut (H.obj X) × Aut (H.obj Y) × V :=
    fun p => (p.1.app X, p.1.app Y, p.2)
  have he : Continuous (autEmbedding H) := continuous_induced_dom
  have hc : Continuous c :=
    ((continuous_apply X).comp (he.comp continuous_fst)).prodMk
      (((continuous_apply Y).comp (he.comp continuous_fst)).prodMk continuous_snd)
  exact (continuous_of_discreteTopology (f := fun p :
    Aut (H.obj X) × Aut (H.obj Y) × V =>
      (fun x => p.2.1.hom (p.2.2 (p.1.inv x)) : V))).comp hc

private def functionContAction (X Y : C) : ContAction FintypeCat.{u} (Aut H) :=
  ⟨functionAction H X Y, functionAction_continuous H X Y⟩

variable {D : Type*} [Category* D] (F : C ⥤ D) (G : D ⥤ FintypeCat.{u})
  (e : H ≅ F ⋙ G)

private def restrictAut (a : Aut G) : Aut H :=
  Aut.autMulEquivOfIso e.symm
    (((Functor.whiskeringLeft C D FintypeCat).obj F).mapAut G a)

private theorem restrictAut_apply (a : Aut G) (X : C) (x : H.obj X) :
    (restrictAut H F G e a).hom.app X x =
      e.inv.app X (a.hom.app (F.obj X) (e.hom.app X x)) := rfl

private theorem restrictAut_inv_apply (a : Aut G) (X : C) (x : H.obj X) :
    (restrictAut H F G e a).inv.app X x =
      e.inv.app X (a.inv.app (F.obj X) (e.hom.app X x)) := rfl

/-- Fixed-point reflection on actual finite objects implies fullness. The
finite function object is obtained from the proved Galois reconstruction. -/
private theorem full_of_fixedPoint_reflection [GaloisCategory C] [FiberFunctor H]
    [G.Faithful]
    (hfixed : ∀ (Z : C) (z : H.obj Z),
      (∀ a : Aut G, a.hom.app (F.obj Z) (e.hom.app Z z) = e.hom.app Z z) →
      ∀ b : Aut H, b.hom.app Z z = z) : F.Full := by
  classical
  constructor
  intro X Y f
  have hinv (W : C) (t : (F ⋙ G).obj W) :
      e.hom.app W (e.inv.app W t) = t :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app W) t
  let h : H.obj X → H.obj Y := fun x =>
    e.inv.app Y (G.map f (e.hom.app X x))
  let A := functionContAction H X Y
  obtain ⟨Z, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (functorToContAction H) A
  have hii : IsIso i.hom.hom.hom :=
    (forget₂ (ContAction FintypeCat (Aut H)) FintypeCat).map_isIso i.hom
  let z : H.obj Z := i.inv.hom.hom h
  have hi : i.hom.hom.hom z = h := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun t => t.hom.hom) i.inv_hom_id) h
  have hres (a : Aut G) :
      ((functionAction H X Y).ρ (restrictAut H F G e a)).hom h = h := by
    funext x
    change e.inv.app Y
      (a.hom.app (F.obj Y) (e.hom.app Y
        (e.inv.app Y (G.map f (e.hom.app X
          (e.inv.app X (a.inv.app (F.obj X) (e.hom.app X x)))))))) = _
    rw [hinv, hinv]
    have hn := ConcreteCategory.congr_hom (a.hom.naturality f)
      (a.inv.app (F.obj X) (e.hom.app X x))
    change a.hom.app (F.obj Y) (G.map f (a.inv.app (F.obj X) (e.hom.app X x))) =
      G.map f (a.hom.app (F.obj X) (a.inv.app (F.obj X) (e.hom.app X x))) at hn
    have ha : a.hom.app (F.obj X) (a.inv.app (F.obj X) (e.hom.app X x)) =
        e.hom.app X x := ConcreteCategory.congr_hom (a.inv_hom_id_app (F.obj X)) _
    rw [ha] at hn
    exact congrArg (e.inv.app Y) hn
  have hzres (a : Aut G) :
      a.hom.app (F.obj Z) (e.hom.app Z z) = e.hom.app Z z := by
    have hz : (restrictAut H F G e a).hom.app Z z = z := by
      apply (ConcreteCategory.bijective_of_isIso i.hom.hom.hom).1
      have heq := ConcreteCategory.congr_hom (i.hom.hom.comm (restrictAut H F G e a)) z
      change i.hom.hom.hom ((restrictAut H F G e a).hom.app Z z) =
        ((functionAction H X Y).ρ (restrictAut H F G e a)).hom (i.hom.hom.hom z) at heq
      rw [hi, hres a] at heq
      exact heq.trans hi.symm
    have := congrArg (e.hom.app Z) hz
    simpa only [restrictAut_apply, ← FintypeCat.comp_apply,
      Category.assoc, e.inv_hom_id_app, Category.comp_id, FintypeCat.id_apply] using this
  have hginv (b : Aut H) : ((functionAction H X Y).ρ b).hom h = h := by
    have heq := ConcreteCategory.congr_hom (i.hom.hom.comm b) z
    change i.hom.hom.hom (b.hom.app Z z) =
      ((functionAction H X Y).ρ b).hom (i.hom.hom.hom z) at heq
    rw [hfixed Z z hzres b, hi] at heq
    exact heq.symm
  let a : (functorToAction H).obj X ⟶ (functorToAction H).obj Y :=
    { hom := FintypeCat.homMk h
      comm := fun b => by
        ext x
        change h (b.hom.app X x) = b.hom.app Y (h x)
        have heq := congrFun (hginv b) (b.hom.app X x)
        change b.hom.app Y (h (b.inv.app X (b.hom.app X x))) =
          h (b.hom.app X x) at heq
        have hb : b.inv.app X (b.hom.app X x) = x :=
          ConcreteCategory.congr_hom (b.hom_inv_id_app X) x
        rw [hb] at heq
        exact heq.symm }
  obtain ⟨g, hg⟩ := (functorToAction H).map_surjective a
  refine ⟨g, G.map_injective ?_⟩
  apply (cancel_epi (e.hom.app X)).mp
  change e.hom.app X ≫ (F ⋙ G).map g = _
  rw [← e.hom.naturality g]
  have hgh : H.map g = FintypeCat.homMk h := congrArg (fun t => t.hom) hg
  rw [hgh]
  ext x
  change e.hom.app Y (e.inv.app Y (G.map f (e.hom.app X x))) = _
  exact hinv Y _

end FiniteActions

section Local

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A local spectrum is connected: all its points specialize to the closed point. -/
private theorem localSpec_connected : ConnectedSpace (Spec (.of R)) := by
  change ConnectedSpace (PrimeSpectrum R)
  apply connectedSpace_iff_clopen.mpr
  refine ⟨⟨IsLocalRing.closedPoint R⟩, ?_⟩
  intro S hS
  by_cases h : IsLocalRing.closedPoint R ∈ S
  · right
    apply Set.eq_univ_of_forall
    intro x
    exact (IsLocalRing.specializes_closedPoint x).mem_open hS.isOpen h
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h ((IsLocalRing.specializes_closedPoint x).mem_closed hS.isClosed hx)

end Local

section Residue

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fixedPoint_reflection {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s₀ : Spec (.of Ω) ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (Z : FiniteEtale (Spec (.of R)))
    (z : Fiber (s₀ ≫ LocalRing.residueSpecMap R) Z)
    (hz : ∀ a : Aut (fiberToFinite s₀),
      a.hom.app ((baseChange (LocalRing.residueSpecMap R)).obj Z)
        ((fiberToFiniteBaseChangeIso (LocalRing.residueSpecMap R) s₀).hom.app Z z) =
        (fiberToFiniteBaseChangeIso (LocalRing.residueSpecMap R) s₀).hom.app Z z) :
    ∀ b : Aut (fiberToFinite (s₀ ≫ LocalRing.residueSpecMap R)), b.hom.app Z z = z := by
  let : ConnectedSpace (Spec (.of (IsLocalRing.ResidueField R))) :=
    localSpec_connected (IsLocalRing.ResidueField R)
  let c := LocalRing.residueSpecMap R
  let B := baseChange c
  let H := fiberToFinite (s₀ ≫ c)
  let G := fiberToFinite s₀
  let T := terminalCover (Spec (.of (IsLocalRing.ResidueField R)))
  let z' : G.obj (B.obj Z) := (fiberToFiniteBaseChangeIso c s₀).hom.app Z z
  let a : (functorToAction G).obj T ⟶ (functorToAction G).obj (B.obj Z) :=
    { hom := FintypeCat.homMk (fun _ => z')
      comm := fun b => by
        ext x
        change z' = b.hom.app (B.obj Z) z'
        exact (hz b).symm }
  let q : T ⟶ B.obj Z := (functorToAction G).preimage a
  have hq : G.map q = FintypeCat.homMk (fun _ : G.obj T => z') :=
    congrArg (fun f => f.hom) ((functorToAction G).map_preimage a)
  let t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Z.obj.left :=
    q.hom.left ≫ pullback.fst Z.obj.hom c
  have ht : t ≫ Z.obj.hom = c := by
    dsimp only [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw := Over.w q.hom
    change q.hom.left ≫ pullback.snd Z.obj.hom c = 𝟙 _ at hw
    rw [hw]
    exact Category.id_comp c
  let pk : G.obj T := Over.homMk s₀ (by change s₀ ≫ 𝟙 _ = s₀; simp)
  have hpoint : s₀ ≫ t = z.left := by
    have heq := congrArg
      (fun p : Fiber s₀ (B.obj Z) => p.left ≫ pullback.fst Z.obj.hom c)
      (ConcreteCategory.congr_hom hq pk)
    change (s₀ ≫ q.hom.left) ≫ pullback.fst Z.obj.hom c =
      ((fiberToFiniteBaseChangeIso c s₀).hom.app Z z).left ≫
        pullback.fst Z.obj.hom c at heq
    rw [Scheme.EtaleFundamentalGroups.finiteBaseChangeIso_hom_apply,
      fiberBaseChangeEquiv_left, pullback.lift_fst] at heq
    exact (Category.assoc _ _ _).symm.trans heq
  obtain ⟨s, ⟨hs, hsr⟩, _⟩ := HenselianResidue.existsUnique_section_lift R Z.obj.hom t ht
  let qR : terminalCover (Spec (.of R)) ⟶ Z := ObjectProperty.homMk (Over.homMk s hs)
  let pR : H.obj (terminalCover (Spec (.of R))) :=
    Over.homMk (s₀ ≫ c) (by change (s₀ ≫ c) ≫ 𝟙 _ = _; simp)
  have hsec : H.map qR pR = z := by
    apply Over.OverMorphism.ext
    change (s₀ ≫ c) ≫ s = z.left
    rw [Category.assoc, hsr]
    exact hpoint
  intro b
  have hb : b.hom.app (terminalCover (Spec (.of R))) pR = pR := by
    apply Over.OverMorphism.ext
    change (b.hom.app (terminalCover (Spec (.of R))) pR).left = s₀ ≫ c
    have hw := Over.w (b.hom.app (terminalCover (Spec (.of R))) pR)
    change (b.hom.app (terminalCover (Spec (.of R))) pR).left ≫ 𝟙 _ = s₀ ≫ c at hw
    simpa only [Category.comp_id] using hw
  calc
    b.hom.app Z z = b.hom.app Z (H.map qR pR) := by rw [hsec]
    _ = H.map qR (b.hom.app (terminalCover (Spec (.of R))) pR) :=
      ConcreteCategory.congr_hom (b.hom.naturality qR) pR
    _ = z := by rw [hb, hsec]

/-- Literal residue base change is full for every Henselian local ring. -/
instance residue_baseChange_full :
    (baseChange (LocalRing.residueSpecMap R)).Full := by
  let : ConnectedSpace (Spec (.of R)) := localSpec_connected R
  let : ConnectedSpace (Spec (.of (IsLocalRing.ResidueField R))) :=
    localSpec_connected (IsLocalRing.ResidueField R)
  let Ω := AlgebraicClosure (IsLocalRing.ResidueField R)
  let s₀ : Spec (.of Ω) ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
    Spec.algebraMap (IsLocalRing.ResidueField R) Ω
  exact full_of_fixedPoint_reflection
    (fiberToFinite (s₀ ≫ LocalRing.residueSpecMap R))
    (baseChange (LocalRing.residueSpecMap R)) (fiberToFinite s₀)
    (fiberToFiniteBaseChangeIso (LocalRing.residueSpecMap R) s₀)
    (fixedPoint_reflection R s₀)

/-- Finite etale covers of a Henselian local spectrum are equivalent to those
of its residue spectrum, by the original base-change functor. -/
instance residue_baseChange_isEquivalence :
    (baseChange (LocalRing.residueSpecMap R)).IsEquivalence where

/-- The equivalence whose forward functor is the literal residue pullback. -/
def residueEquivalence :
    FiniteEtale (Spec (.of R)) ≌ FiniteEtale (Spec (.of (IsLocalRing.ResidueField R))) :=
  (baseChange (LocalRing.residueSpecMap R)).asEquivalence

@[simp] theorem residueEquivalence_functor :
    (residueEquivalence R).functor = baseChange (LocalRing.residueSpecMap R) := rfl

@[simp] theorem residueEquivalence_functor_obj_hom (Y : FiniteEtale (Spec (.of R))) :
    ((residueEquivalence R).functor.obj Y).obj.hom =
      pullback.snd Y.obj.hom (LocalRing.residueSpecMap R) := rfl

@[reassoc] theorem residueEquivalence_functor_map_fst
    {Y Z : FiniteEtale (Spec (.of R))} (f : Y ⟶ Z) :
    ((residueEquivalence R).functor.map f).hom.left ≫
        pullback.fst Z.obj.hom (LocalRing.residueSpecMap R) =
      pullback.fst Y.obj.hom (LocalRing.residueSpecMap R) ≫ f.hom.left :=
  pullback.lift_fst _ _ _

end Residue

end AlgebraicGeometry.Scheme.FiniteEtale.HenselianEquivalence
