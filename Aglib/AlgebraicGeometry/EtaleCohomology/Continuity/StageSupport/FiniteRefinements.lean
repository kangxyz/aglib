/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StageSupport.AffineRefinements
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SupportedFamilyAcyclic

/-!
# Finite supported refinements of original small étale covering sieves

A qcqs stage model has a finite affine étale covering family. Pulling this
family to the limit gives affine modeled charts. Finite supported refinements
of the original sieve on those charts are bound together in the original site.
The support predicate is not identified with all qcqs objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]

include hc

/-- A covering sieve of a stage-supported target contains a finite supported
covering family, retaining literal membership in the original sieve. -/
theorem exists_finite_stage_supported_family {W : c.pt.unop.Etale}
    (hW : stageDescendedQcqsObjects X c W)
    (R : Sieve W) (hR : R ∈ c.pt.unop.smallEtaleTopology W) :
    ∃ (J : Type u) (_ : Finite J) (U : J → Over W),
      (∀ j, stageDescendedQcqsObjects X c (U j).left) ∧
      Sieve.ofArrows (fun j => (U j).left) (fun j => (U j).hom) ∈
        c.pt.unop.smallEtaleTopology W ∧
      ∀ j, R (U j).hom := by
  classical
  obtain ⟨i, ⟨M⟩⟩ := hW
  let : CompactSpace M.obj.left := M.compactSpace
  obtain ⟨J, hJ, V, f, hV, _, hcover⟩ :=
    EtaleAffineBasis.exists_finite_affine_family M.obj ⊤
      ((X.obj i).unop.smallEtaleTopology.top_mem M.obj)
  let : Finite J := hJ
  have (j : J) : IsAffine (V j).left := hV j
  let p : c.pt.unop ⟶ (X.obj i).unop := (c.ι.app i).unop
  let F : (X.obj i).unop.Etale ⥤ c.pt.unop.Etale := siteBaseChange p
  let B : J → c.pt.unop.Etale := fun j => F.obj (V j)
  let b (j : J) : B j ⟶ W := F.map (f j) ≫ M.iso.hom
  let MB (j : J) : StageSupport.Model X c i (B j) :=
    { obj := V j
      compactSpace := inferInstanceAs (CompactSpace (V j).left)
      quasiSeparatedSpace := inferInstanceAs (QuasiSeparatedSpace (V j).left)
      iso := Iso.refl _ }
  have (j : J) : IsAffine (MB j).obj.left := hV j
  have hbase : Sieve.ofArrows B (fun j => F.map (f j)) ∈
      c.pt.unop.smallEtaleTopology (F.obj M.obj) := by
    simpa only [Sieve.functorPushforward_ofArrows] using
      (siteBaseChange_coverPreserving (X := (X.obj i).unop) (S := c.pt.unop) p).cover_preserve
        hcover
  have hB : Sieve.ofArrows B b ∈ c.pt.unop.smallEtaleTopology W := by
    apply c.pt.unop.smallEtaleTopology.superset_covering ?_
      (c.pt.unop.smallEtaleTopology.pullback_stable M.iso.inv hbase)
    intro Z g hg
    obtain ⟨j, a, ha⟩ := (Sieve.mem_ofArrows_iff B (fun j => F.map (f j))
      (g ≫ M.iso.inv)).mp hg
    apply (Sieve.mem_ofArrows_iff B b g).mpr
    refine ⟨j, a, ?_⟩
    calc
      g = (g ≫ M.iso.inv) ≫ M.iso.hom := by simp
      _ = (a ≫ F.map (f j)) ≫ M.iso.hom := congrArg (fun q => q ≫ M.iso.hom) ha
      _ = a ≫ b j := Category.assoc _ _ _
  have hlocal (j : J) : ∃ (K : Type u) (_ : Finite K) (U : K → Over (B j)),
      (∀ k, stageDescendedQcqsObjects X c (U k).left) ∧
      Sieve.ofArrows (fun k => (U k).left) (fun k => (U k).hom) ∈
        c.pt.unop.smallEtaleTopology (B j) ∧
      ∀ k, (R.pullback (b j)) (U k).hom :=
    StageSupport.exists_affine_supported_family hc (MB j) (R.pullback (b j))
      (c.pt.unop.smallEtaleTopology.pullback_stable (b j) hR)
  choose K hK U hU hcov hmem using hlocal
  let (j : J) : Finite (K j) := hK j
  let T : (Σ j, K j) → Over W := fun p => Over.mk ((U p.1 p.2).hom ≫ b p.1)
  refine ⟨Σ j, K j, inferInstance, T, fun p => hU p.1 p.2, ?_, fun p => hmem p.1 p.2⟩
  have hbind := c.pt.unop.smallEtaleTopology.bindOfArrows
    (R := fun j => Presieve.ofArrows (fun k => (U j k).left) (fun k => (U j k).hom))
    hB hcov
  have hT : Sieve.generate (Presieve.bindOfArrows B b
      (fun j => Presieve.ofArrows (fun k => (U j k).left) (fun k => (U j k).hom))) =
      Sieve.ofArrows (fun q => (T q).left) (fun q => (T q).hom) := by
    rw [Presieve.bindOfArrows_ofArrows]
    rfl
  exact hT ▸ hbind

/-- The exact finite-supported-refinement condition for the original limit
small étale topology. The universe lift changes only the finite indexing type. -/
theorem stageDescendedQcqsObjects_finiteRefinements :
    CategoryTheory.Sheaf.ModuleCoefficients.HasFiniteSupportedRefinements
      (J := c.pt.unop.smallEtaleTopology) (stageDescendedQcqsObjects X c) := by
  intro W hW R hR
  obtain ⟨J, hJ, U, hU, hcover, hmem⟩ :=
    exists_finite_stage_supported_family X c hc hW R hR
  let : Finite J := hJ
  let V : ULift.{u + 1} J → Over W := fun j => U j.down
  refine ⟨ULift.{u + 1} J, inferInstance, V, fun j => hU j.down, ?_, fun j => hmem j.down⟩
  apply c.pt.unop.smallEtaleTopology.superset_covering (S :=
    Sieve.ofArrows (fun j => (U j).left) (fun j => (U j).hom)) ?_ hcover
  intro Z g hg
  obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  exact (Sieve.ofArrows (fun j => (V j).left) (fun j => (V j).hom)).downward_closed
    (Sieve.ofArrows_mk _ _ (ULift.up j)) a

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
