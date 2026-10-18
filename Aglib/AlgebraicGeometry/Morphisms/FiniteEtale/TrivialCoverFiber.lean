/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant

/-! Every field-valued fibre of the actual labelled trivial cover is the
label set, including the empty label set. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber)

universe u
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The fiber point of the trivial cover obtained by placing `q` in the summand indexed by `a`. -/
def trivialCoverFiberPoint (A : Type u) [Finite A]
    (q : Spec (CommRingCat.of Ω) ⟶ X) (a : A) : Fiber q (trivialCover X A) :=
  Over.homMk (q ≫ (trivialCoverι X A a).hom.left) (by
    rw [Category.assoc, trivialCoverι_struct, Category.comp_id]
    rfl)

theorem trivialCoverFiberPoint_sigma (A : Type u) [Finite A]
    (q : Spec (CommRingCat.of Ω) ⟶ X) (a : A) :
    (trivialCoverFiberPoint A q a).left ≫ (trivialCoverSigmaIso X A).hom =
      q ≫ Sigma.ι (fun _ : A => X) a := by
  change (q ≫ (trivialCoverι X A a).hom.left) ≫ (trivialCoverSigmaIso X A).hom = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f : X ⟶ ∐ fun _ : A => X => q ≫ f)
      (trivialCoverSigmaIso_ι X A a))

theorem trivialCoverFiberPoint_injective (A : Type u) [Finite A]
    (q : Spec (CommRingCat.of Ω) ⟶ X) : Function.Injective (trivialCoverFiberPoint A q) := by
  intro a b h
  have hc := congrArg (fun p : Fiber q (trivialCover X A) =>
    p.left ≫ (trivialCoverSigmaIso X A).hom) h
  rw [trivialCoverFiberPoint_sigma, trivialCoverFiberPoint_sigma] at hc
  have hp := congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ ∐ fun _ : A => X =>
    f (default : Spec (CommRingCat.of Ω))) hc
  have hi := (sigmaι_eq_iff (g := fun _ : A => X) a b
    (q (default : Spec (CommRingCat.of Ω))) (q (default : Spec (CommRingCat.of Ω)))).mp hp
  exact congrArg (fun p : Σ _ : A, X => p.1) hi

theorem trivialCoverFiberPoint_surjective (A : Type u) [Finite A]
    (q : Spec (CommRingCat.of Ω) ⟶ X) : Function.Surjective (trivialCoverFiberPoint A q) := by
  intro p
  let psigma : Spec (CommRingCat.of Ω) ⟶ ∐ fun _ : A => X :=
    p.left ≫ (trivialCoverSigmaIso X A).hom
  obtain ⟨⟨a, z⟩, hz⟩ := (sigmaMk (fun _ : A => X)).surjective
    (psigma (default : Spec (CommRingCat.of Ω)))
  have hrange : Set.range psigma ⊆ Set.range (Sigma.ι (fun _ : A => X) a) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨z, ?_⟩
    rw [Subsingleton.elim x (default : Spec (CommRingCat.of Ω))]
    simpa only [sigmaMk_mk] using hz
  let r : Spec (CommRingCat.of Ω) ⟶ X :=
    IsOpenImmersion.lift (Sigma.ι (fun _ : A => X) a) psigma hrange
  have hfac : r ≫ Sigma.ι (fun _ : A => X) a = psigma :=
    IsOpenImmersion.lift_fac _ _ _
  have hsection : p.left = r ≫ (trivialCoverι X A a).hom.left := by
    apply (cancel_mono (trivialCoverSigmaIso X A).hom).mp
    exact hfac.symm.trans ((congrArg (fun f : X ⟶ ∐ fun _ : A => X => r ≫ f)
      (trivialCoverSigmaIso_ι X A a).symm).trans (Category.assoc _ _ _).symm)
  have hr : r = q := by
    calc
      r = r ≫ 𝟙 X := (Category.comp_id r).symm
      _ = r ≫ ((trivialCoverι X A a).hom.left ≫ (trivialCover X A).obj.hom) :=
        congrArg (fun f : X ⟶ X => r ≫ f) (trivialCoverι_struct X A a).symm
      _ = (r ≫ (trivialCoverι X A a).hom.left) ≫ (trivialCover X A).obj.hom :=
        (Category.assoc _ _ _).symm
      _ = p.left ≫ (trivialCover X A).obj.hom :=
        congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ (trivialCover X A).obj.left =>
          f ≫ (trivialCover X A).obj.hom) hsection.symm
      _ = q := Over.w p
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  change q ≫ (trivialCoverι X A a).hom.left = p.left
  exact (congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ X =>
    f ≫ (trivialCoverι X A a).hom.left) hr.symm).trans hsection.symm

/-- The equivalence sending an index to the corresponding fiber point of the trivial cover. -/
def trivialCoverFiberEquiv (A : Type u) [Finite A]
    (q : Spec (CommRingCat.of Ω) ⟶ X) : A ≃ Fiber q (trivialCover X A) :=
  Equiv.ofBijective (trivialCoverFiberPoint A q)
    ⟨trivialCoverFiberPoint_injective A q, trivialCoverFiberPoint_surjective A q⟩

theorem trivialCoverFiber_isEmpty (A : Type u) [Finite A] [IsEmpty A]
    (q : Spec (CommRingCat.of Ω) ⟶ X) : IsEmpty (Fiber q (trivialCover X A)) :=
  ⟨fun p => isEmptyElim ((trivialCoverFiberEquiv A q).symm p)⟩

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f74d3899da0dfe3bc99679b65527c067c287897d8294719d0c4334beab8c05ec.
Definitions, hypotheses and universes are retained modulo native names. -/
