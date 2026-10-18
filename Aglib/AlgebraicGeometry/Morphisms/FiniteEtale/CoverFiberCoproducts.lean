/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverCoproductPreservation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Fiber
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! A field-valued point of a finite coproduct lies in one unique component.
This proves finite coproduct preservation for the actual point-lift fibre,
including empty coproducts, without a Galois-category or representability input. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiber fiberToFinite
  fiberToFiniteForgetIso forgetToScheme)

universe u
variable {X : Scheme.{u}} {I : Type} [Finite I] (Y : I → Scheme.FiniteEtale X)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)

/-- The canonical isomorphism from the underlying scheme of a finite cover coproduct to the
coproduct of its underlying schemes. -/
def coverCoproductSchemeIso :
    (∐ Y : Scheme.FiniteEtale X).obj.left ≅ ∐ (fun i => (Y i).obj.left) :=
  PreservesCoproduct.iso (forgetToScheme X) Y

theorem coverCoproductSchemeIso_ι (i : I) :
    (Sigma.ι Y i).hom.left ≫ (coverCoproductSchemeIso Y).hom =
      Sigma.ι (fun i => (Y i).obj.left) i := by
  have h := map_ι_comp_inv_sigmaComparison (forgetToScheme X) Y i
  change (forgetToScheme X).map (Sigma.ι Y i) ≫
    (PreservesCoproduct.iso (forgetToScheme X) Y).hom =
      Sigma.ι (fun i => (forgetToScheme X).obj (Y i)) i
  simpa only [← PreservesCoproduct.inv_hom, IsIso.Iso.inv_inv] using h

/-- The fibre point of the coproduct obtained by composing a summand fibre point with its
coproduct inclusion. -/
def fiberCoproductPoint : (Σ i, Fiber s (Y i)) → Fiber s (∐ Y) :=
  fun p => p.2 ≫ (Sigma.ι Y p.1).hom

theorem fiberCoproductPoint_scheme (p : Σ i, Fiber s (Y i)) :
    (fiberCoproductPoint Y s p).left ≫ (coverCoproductSchemeIso Y).hom =
      p.2.left ≫ Sigma.ι (fun i => (Y i).obj.left) p.1 := by
  change (p.2.left ≫ (Sigma.ι Y p.1).hom.left) ≫ _ = _
  rw [Category.assoc, coverCoproductSchemeIso_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fiberCoproductPoint_injective : Function.Injective (fiberCoproductPoint Y s) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ hpq
  have hm := congrArg (fun p : Fiber s (∐ Y) => p.left ≫ (coverCoproductSchemeIso Y).hom) hpq
  rw [fiberCoproductPoint_scheme, fiberCoproductPoint_scheme] at hm
  have hx := congrArg (fun f : Spec (CommRingCat.of K) ⟶ ∐ (fun i => (Y i).obj.left) =>
    f default) hm
  have hij : i = j := congrArg (fun a : Σ i, (Y i).obj.left => a.1)
    ((sigmaι_eq_iff (g := fun i => (Y i).obj.left) i j
      (p.left (default : Spec (CommRingCat.of K)))
      (q.left (default : Spec (CommRingCat.of K)))).mp hx)
  subst j
  have hpq' : p = q := by
    apply Over.OverMorphism.ext
    exact (cancel_mono (Sigma.ι (fun i => (Y i).obj.left) i)).mp hm
  subst q
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fiberCoproductPoint_surjective : Function.Surjective (fiberCoproductPoint Y s) := by
  intro p
  let psigma : Spec (CommRingCat.of K) ⟶ ∐ (fun i => (Y i).obj.left) :=
    p.left ≫ (coverCoproductSchemeIso Y).hom
  obtain ⟨i, z, hz⟩ := (sigmaOpenCover (fun i => (Y i).obj.left)).exists_eq (psigma default)
  have hrange : Set.range psigma ⊆ Set.range (Sigma.ι (fun i => (Y i).obj.left) i) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨z, ?_⟩
    rw [Subsingleton.elim x (default : Spec (CommRingCat.of K))]
    exact hz
  let r := IsOpenImmersion.lift (Sigma.ι (fun i => (Y i).obj.left) i) psigma hrange
  have hfac : r ≫ Sigma.ι (fun i => (Y i).obj.left) i = psigma :=
    IsOpenImmersion.lift_fac _ _ _
  have hsection : p.left = r ≫ (Sigma.ι Y i).hom.left := by
    apply (cancel_mono (coverCoproductSchemeIso Y).hom).mp
    rw [Category.assoc, coverCoproductSchemeIso_ι]
    exact hfac.symm
  have hr : r ≫ (Y i).obj.hom = s := by
    rw [← Over.w (Sigma.ι Y i).hom, ← Category.assoc, ← hsection]
    exact Over.w p
  refine ⟨⟨i, Over.homMk r hr⟩, ?_⟩
  apply Over.OverMorphism.ext
  exact hsection.symm

/-- The coproduct colimit structure on the fibre of a finite coproduct, with maps induced by the
cover inclusions. -/
def fiberCoproductIsColimit :
    IsColimit (Cofan.mk (Fiber s (∐ Y)) (fun i => (fiber s).map (Sigma.ι Y i))) := by
  apply Classical.choice
  rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma]
  exact ⟨fiberCoproductPoint_injective Y s, fiberCoproductPoint_surjective Y s⟩

instance fiber_preservesCoproduct : PreservesColimit (Discrete.functor Y) (fiber s) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct Y)
    ((isColimitMapCoconeCofanMkEquiv (fiber s) Y (Sigma.ι Y)).symm
      (fiberCoproductIsColimit Y s))

instance fiber_preservesFiniteCoproducts : PreservesFiniteCoproducts (fiber s) where
  preserves n := by
    refine ⟨fun {D} => ?_⟩
    have := fiber_preservesCoproduct (fun i : Fin n => D.obj ⟨i⟩) s
    exact preservesColimit_of_iso_diagram (fiber s)
      (Discrete.natIso (F := Discrete.functor (fun i : Fin n => D.obj ⟨i⟩))
        (G := D) (fun _ => Iso.refl _))

instance fiberToFinite_preservesFiniteCoproducts : PreservesFiniteCoproducts (fiberToFinite s) := by
  have : PreservesFiniteCoproducts (fiberToFinite s ⋙ FintypeCat.incl) :=
    ⟨fun _ => preservesColimitsOfShape_of_natIso (fiberToFiniteForgetIso s).symm⟩
  exact preservesFiniteCoproducts_of_reflects_of_preserves (fiberToFinite s) FintypeCat.incl

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c2afeb98278ba2847d4034d392de1dbc8b6a775dbcec334a856ac0180bcb13ba.
Definitions, hypotheses and universes are retained modulo native names. -/
