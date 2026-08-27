import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import MorganTianLib.Ch01.Curvature.Sectional

/-!
# Intrinsic sectional planes

This module supplies the plane-level quotient missing from the ordered-pair
API in `Curvature.Sectional`.  A `SectionalPlaneBasis` is an independent
ordered pair, and `SectionalPlane` identifies two such pairs when one is an
invertible `GL₂(ℝ)` change of generators.  Thus a value descended to
`SectionalPlane` is independent of the chosen generators, while retaining an
explicit representative for decomposable calculations.

The diagonal quotient and its bilinear-form variant are the intrinsic core of
Morgan--Tian Definition 1.6 and Definition 1.7 (`morganTian2007`).  The
Gram-determinant normalization is cross-checked against do Carmo, Chapter 4,
Section 3 (`doCarmo1992`), and Petersen, Chapter 3 (`petersen2016`).  No chart,
frame, connection, or selected extension occurs here.  The tangent-space
producer remains the direct-only witness-indexed adapter in
`Curvature.SectionalProvisional`.

The relation is presented explicitly rather than through a quotient of a
submodule lattice: its determinant witness is the checked finite-dimensional
`GL₂` change-of-generators law already proved in `Curvature.Sectional`.
`sectionalPlaneChange_span` records the underlying span equality.
-/

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-! ### Independent generators and the plane quotient -/

/-- An ordered pair of generators for a genuine two-plane. -/
structure SectionalPlaneBasis (U : Type*) [AddCommGroup U] [Module ℝ U] where
  x : U
  y : U
  independent : LinearIndependent ℝ ![x, y]

/-- The same plane basis with its two generators interchanged. -/
def SectionalPlaneBasis.swap (p : SectionalPlaneBasis U) :
    SectionalPlaneBasis U :=
  ⟨p.y, p.x, by
    have hi := p.independent.comp (Equiv.swap 0 1) (Equiv.swap 0 1).injective
    have he : (fun i => ![p.x, p.y] ((Equiv.swap 0 1) i)) = ![p.y, p.x] := by
      funext i
      fin_cases i
      · change ![p.x, p.y] ((Equiv.swap 0 1) 0) = p.y
        rw [Equiv.swap_apply_left]
        rfl
      · change ![p.x, p.y] ((Equiv.swap 0 1) 1) = p.x
        rw [Equiv.swap_apply_right]
        rfl
    rw [← he]
    exact hi⟩

/-- One invertible change of ordered generators.  The rows of the displayed
matrix give the new first and second generators respectively. -/
def sectionalPlaneChange (p q : SectionalPlaneBasis U) : Prop :=
  ∃ a b c d : ℝ,
    a * d - b * c ≠ 0 ∧
      q.x = a • p.x + b • p.y ∧
      q.y = c • p.x + d • p.y

private lemma sectionalPlaneChange_symm {p q : SectionalPlaneBasis U}
    (h : sectionalPlaneChange p q) : sectionalPlaneChange q p := by
  rcases h with ⟨a, b, c, d, hdet, hqx, hqy⟩
  let Δ : ℝ := a * d - b * c
  refine ⟨d / Δ, -b / Δ, -c / Δ, a / Δ, ?_, ?_, ?_⟩
  · have hΔ : Δ ≠ 0 := by simpa [Δ] using hdet
    have hda : d * a - b * c ≠ 0 := by simpa [mul_comm] using hdet
    have hcalc : (d / Δ) * (a / Δ) - (-b / Δ) * (-c / Δ) =
        (d * a - b * c) / Δ ^ 2 := by
      field_simp [hΔ]
    rw [hcalc]
    exact div_ne_zero hda (pow_ne_zero 2 hΔ)
  · rw [hqx, hqy]
    have hΔ : Δ ≠ 0 := by simpa [Δ] using hdet
    have h₁ : d / Δ * a - b / Δ * c = 1 := by
      field_simp [hΔ]
      dsimp [Δ]
      ring
    have h₂ : d / Δ * b - b / Δ * d = 0 := by ring
    calc
      p.x = (d / Δ * a - b / Δ * c) • p.x +
          (d / Δ * b - b / Δ * d) • p.y := by rw [h₁, h₂]; simp
      _ = (d / Δ) • (a • p.x + b • p.y) +
          (-b / Δ) • (c • p.x + d • p.y) := by module
  · rw [hqx, hqy]
    have hΔ : Δ ≠ 0 := by simpa [Δ] using hdet
    have h₁ : -c / Δ * a + a / Δ * c = 0 := by ring
    have h₂ : -c / Δ * b + a / Δ * d = 1 := by
      field_simp [hΔ]
      dsimp [Δ]
      ring
    calc
      p.y = (-c / Δ * a + a / Δ * c) • p.x +
          (-c / Δ * b + a / Δ * d) • p.y := by rw [h₁, h₂]; simp
      _ = (-c / Δ) • (a • p.x + b • p.y) +
          (a / Δ) • (c • p.x + d • p.y) := by module

private lemma sectionalPlaneChange_trans {p q r : SectionalPlaneBasis U}
    (hpq : sectionalPlaneChange p q) (hqr : sectionalPlaneChange q r) :
    sectionalPlaneChange p r := by
  rcases hpq with ⟨a, b, c, d, hdet, hqx, hqy⟩
  rcases hqr with ⟨e, f, g, h, hdet', hrx, hry⟩
  refine ⟨e * a + f * c, e * b + f * d, g * a + h * c, g * b + h * d,
    ?_, ?_, ?_⟩
  · rw [show (e * a + f * c) * (g * b + h * d) -
      (e * b + f * d) * (g * a + h * c) =
      (e * h - f * g) * (a * d - b * c) by ring]
    exact mul_ne_zero hdet' hdet
  · rw [hrx, hqx, hqy]
    module
  · rw [hry, hqx, hqy]
    module

/-- If two independent ordered pairs are related by a change of generators,
the change matrix necessarily has nonzero determinant. -/
private lemma det_ne_of_independent_change {p q : SectionalPlaneBasis U}
    {a b c d : ℝ} (hqx : q.x = a • p.x + b • p.y)
    (hqy : q.y = c • p.x + d • p.y) : a * d - b * c ≠ 0 := by
  intro hdet
  have hq := (linearIndependent_fin2.mp q.independent)
  have hqy_not : ∀ t : ℝ, t • q.y ≠ q.x := hq.2
  by_cases hc : c = 0
  · have had : a * d = 0 := by simpa [hc] using hdet
    by_cases ha : a = 0
    · by_cases hd : d = 0
      · apply hq.1
        rw [hqy, hc, hd]
        simp
      · apply hqy_not (b / d)
        rw [hqx, hqy, ha, hc]
        simp only [zero_smul, zero_add, smul_smul]
        rw [div_mul_cancel₀ b hd]
    · have hd : d = 0 := (mul_eq_zero.mp had).resolve_left ha
      apply hq.1
      rw [hqy, hc, hd]
      simp
  · apply hqy_not (a / c)
    rw [hqx, hqy]
    simp only [smul_add, smul_smul]
    have hcc : a / c * c = a := div_mul_cancel₀ a hc
    have hcd : a / c * d = b := by
      field_simp [hc]
      nlinarith [hdet]
    rw [hcc, hcd]

private lemma sectionalPlaneChange_equiv :
    Equivalence (sectionalPlaneChange (U := U)) where
  refl p := ⟨1, 0, 0, 1, by norm_num, by simp, by simp⟩
  symm := by
    intro p q h
    exact sectionalPlaneChange_symm h
  trans := by
    intro p q r hpq hqr
    exact sectionalPlaneChange_trans hpq hqr

/-- The setoid of independent ordered generators modulo invertible changes. -/
def sectionalPlaneSetoid (U : Type*) [AddCommGroup U] [Module ℝ U] :
    Setoid (SectionalPlaneBasis U) where
  r := sectionalPlaneChange
  iseqv := sectionalPlaneChange_equiv

/-- An intrinsic (unoriented) tangent two-plane represented by independent
ordered generators modulo `GL₂(ℝ)`. -/
def SectionalPlane (U : Type*) [AddCommGroup U] [Module ℝ U] :=
  Quotient (sectionalPlaneSetoid U)

/-- Put an independent ordered pair into the intrinsic plane quotient. -/
def sectionalPlaneMk (p : SectionalPlaneBasis U) : SectionalPlane U :=
  Quotient.mk (sectionalPlaneSetoid U) p

/-- The span carried by an ordered plane representative. -/
def SectionalPlaneBasis.span (p : SectionalPlaneBasis U) : Submodule ℝ U :=
  Submodule.span ℝ (Set.range ![p.x, p.y])

/-- An invertible change of generators preserves the represented subspace. -/
theorem sectionalPlaneChange_span {p q : SectionalPlaneBasis U}
    (h : sectionalPlaneChange p q) : p.span = q.span := by
  have hle : ∀ {r s : SectionalPlaneBasis U}, sectionalPlaneChange r s →
      s.span ≤ r.span := by
    intro r s hrs
    rcases hrs with ⟨a, b, c, d, _hdet, hrx, hry⟩
    change Submodule.span ℝ (Set.range ![s.x, s.y]) ≤
      Submodule.span ℝ (Set.range ![r.x, r.y])
    rw [Submodule.span_le]
    intro v hv
    rcases hv with ⟨i, rfl⟩
    fin_cases i
    · rw [hrx]
      have hs0 : r.x ∈ Submodule.span ℝ (Set.range ![r.x, r.y]) :=
        Submodule.subset_span (Set.mem_range_self 0)
      have hs1 : r.y ∈ Submodule.span ℝ (Set.range ![r.x, r.y]) :=
        Submodule.subset_span (Set.mem_range_self 1)
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a hs0) (Submodule.smul_mem _ b hs1)
    · rw [hry]
      have hs0 : r.x ∈ Submodule.span ℝ (Set.range ![r.x, r.y]) :=
        Submodule.subset_span (Set.mem_range_self 0)
      have hs1 : r.y ∈ Submodule.span ℝ (Set.range ![r.x, r.y]) :=
        Submodule.subset_span (Set.mem_range_self 1)
      exact Submodule.add_mem _
        (Submodule.smul_mem _ c hs0) (Submodule.smul_mem _ d hs1)
  exact le_antisymm (hle (sectionalPlaneChange_symm h)) (hle h)

/-- For independent pairs, equality of the generated subspaces is equivalent
to an invertible `GL₂` change of generators. -/
theorem sectionalPlaneChange_iff_span_eq {p q : SectionalPlaneBasis U} :
    sectionalPlaneChange p q ↔ p.span = q.span := by
  constructor
  · exact sectionalPlaneChange_span
  · intro hspan
    have hpx : q.x ∈ p.span := by
      rw [hspan]
      exact Submodule.subset_span (by
        exact Set.mem_range_self 0)
    have hpy : q.y ∈ p.span := by
      rw [hspan]
      exact Submodule.subset_span (by
        exact Set.mem_range_self 1)
    have hp_span : p.span = Submodule.span ℝ ({p.x, p.y} : Set U) := by
      apply congrArg (Submodule.span ℝ)
      ext z
      change (∃ i : Fin 2, ![p.x, p.y] i = z) ↔ z = p.x ∨ z = p.y
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl hi.symm
        · exact Or.inr hi.symm
      · intro hz
        rcases hz with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hp_span] at hpx hpy
    rcases (Submodule.mem_span_pair.mp hpx) with ⟨a, b, hab⟩
    rcases (Submodule.mem_span_pair.mp hpy) with ⟨c, d, hcd⟩
    refine ⟨a, b, c, d, ?_, hab.symm, hcd.symm⟩
    exact det_ne_of_independent_change hab.symm hcd.symm

/-- Quotient equality is exactly equality of the represented two-dimensional
subspaces. -/
theorem sectionalPlaneMk_eq_iff_span_eq {p q : SectionalPlaneBasis U} :
    sectionalPlaneMk p = sectionalPlaneMk q ↔ p.span = q.span := by
  constructor
  · intro h
    exact sectionalPlaneChange_span (Quotient.exact h)
  · intro h
    exact Quotient.sound (sectionalPlaneChange_iff_span_eq.mpr h)

/-- The underlying subspace of an intrinsic plane. -/
noncomputable def sectionalPlaneSpan : SectionalPlane U → Submodule ℝ U :=
  Quotient.lift SectionalPlaneBasis.span (by
    intro p q hpq
    exact sectionalPlaneChange_span hpq)

/-- The span evaluator reduces to the span of a chosen representative. -/
@[simp] theorem sectionalPlaneSpan_mk (p : SectionalPlaneBasis U) :
    sectionalPlaneSpan (sectionalPlaneMk p) = p.span := by
  rfl

/-- Equality in the quotient is exactly an invertible change of generators. -/
@[simp] theorem sectionalPlaneMk_eq_iff {p q : SectionalPlaneBasis U} :
    sectionalPlaneMk p = sectionalPlaneMk q ↔ sectionalPlaneChange p q := by
  exact Quotient.eq

/-- Swapping the generators is an allowed determinant `-1` change. -/
theorem sectionalPlaneChange_swap (p : SectionalPlaneBasis U) :
    sectionalPlaneChange p p.swap := by
  refine ⟨0, 1, 1, 0, by norm_num, ?_, ?_⟩ <;> simp [SectionalPlaneBasis.swap]

/-- The quotient forgets the ordering of the two generators. -/
theorem sectionalPlaneMk_swap (p : SectionalPlaneBasis U) :
    sectionalPlaneMk p.swap = sectionalPlaneMk p := by
  apply (sectionalPlaneMk_eq_iff).mpr
  exact sectionalPlaneChange_symm (sectionalPlaneChange_swap p)

/-! ### Descending diagonal forms to a plane -/

private def planeValue (f : SectionalPlaneBasis U → ℝ)
    (hf : ∀ {p q}, sectionalPlaneChange p q → f p = f q) : SectionalPlane U → ℝ :=
  Quotient.lift f (by
    intro p q hpq
    exact hf hpq)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Sectional curvature evaluated on an intrinsic plane.  The algebraic
curvature witness is the only hypothesis needed to descend the quotient. -/
def sectionalCurvaturePlane {B : W → W → W → W → ℝ}
    (hB : IsAlgebraicCurvature B) : SectionalPlane W → ℝ :=
  planeValue (fun p => sectionalCurvature B p.x p.y) (by
    intro p q hpq
    rcases hpq with ⟨a, b, c, d, hdet, hqx, hqy⟩
    rw [hqx, hqy]
    simpa [sectionalCurvature] using
      (sectionalCurvature_changeBasis hB a b c d p.x p.y hdet).symm)

/-- The intrinsic evaluator reduces to the normalized representative value. -/
@[simp] theorem sectionalCurvaturePlane_mk {B : W → W → W → W → ℝ}
    (hB : IsAlgebraicCurvature B) (p : SectionalPlaneBasis W) :
    sectionalCurvaturePlane hB (sectionalPlaneMk p) = sectionalCurvature B p.x p.y := by
  rfl

/-- Generator-independence of the inner-product sectional quotient. -/
theorem sectionalCurvaturePlane_basis_independent {B : W → W → W → W → ℝ}
    (hB : IsAlgebraicCurvature B) {p q : SectionalPlaneBasis W}
    (hpq : sectionalPlaneChange p q) :
    sectionalCurvature B p.x p.y = sectionalCurvature B q.x q.y := by
  rcases hpq with ⟨a, b, c, d, hdet, hqx, hqy⟩
  rw [hqx, hqy]
  simpa [sectionalCurvature] using
    (sectionalCurvature_changeBasis hB a b c d p.x p.y hdet).symm

/-- The descended evaluator gives the same value for any two representatives
of an equal quotient plane. -/
theorem sectionalCurvaturePlane_eq_of_eq {B : W → W → W → W → ℝ}
    (hB : IsAlgebraicCurvature B) {p q : SectionalPlaneBasis W}
    (h : sectionalPlaneMk p = sectionalPlaneMk q) :
    sectionalCurvature B p.x p.y = sectionalCurvature B q.x q.y := by
  simpa only [sectionalCurvaturePlane_mk] using
    (congrArg (sectionalCurvaturePlane hB) h)

/-- Interchanging the two generators leaves sectional curvature unchanged. -/
theorem sectionalCurvaturePlane_swap {B : W → W → W → W → ℝ}
    (hB : IsAlgebraicCurvature B) (p : SectionalPlaneBasis W) :
    sectionalCurvaturePlane hB (sectionalPlaneMk p.swap) =
      sectionalCurvaturePlane hB (sectionalPlaneMk p) := by
  rw [sectionalPlaneMk_swap]

/-- The constant-curvature model has value `lam` on every represented plane,
not just on an orthonormal representative. -/
theorem sectionalCurvaturePlane_model (lam : ℝ)
    (p : SectionalPlaneBasis W) :
    sectionalCurvaturePlane
        (isAlgebraicCurvature_modelCurvature4 (W := W) lam)
        (sectionalPlaneMk p) = lam := by
  rw [sectionalCurvaturePlane_mk]
  unfold sectionalCurvature
  rw [modelCurvature4]
  have hpos : 0 < wedgeSq p.x p.y :=
    (wedgeSq_pos_iff_linearIndependent p.x p.y).mpr p.independent
  simp only [real_inner_comm p.y p.x, wedgeSq]
  have hden : inner ℝ p.x p.x * inner ℝ p.y p.y -
      inner ℝ p.y p.x ^ 2 ≠ 0 := by
    simpa [wedgeSq, real_inner_comm, pow_two] using (ne_of_gt hpos)
  field_simp [hden]

/-! ### Tangent-space-compatible plain bilinear form -/

/-- The bilinear-form version of the plane quotient.  This is the form used
by a bundled tangent metric, whose fibres intentionally do not receive a
second `InnerProductSpace` instance. -/
def sectionalCurvatureBilinPlane {B : U → U → U → U → ℝ}
    (hB : IsAlgebraicCurvature B) (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (_hG : ∀ x y, G x y = G y x) : SectionalPlane U → ℝ :=
  planeValue (fun p => B p.x p.y p.x p.y / wedgePairingDiag G p.x p.y) (by
    intro p q hpq
    rcases hpq with ⟨a, b, c, d, hdet, hqx, hqy⟩
    rw [hqx, hqy]
    simpa [wedgePairingDiag] using
      (sectionalCurvatureBilin_changeBasis hB G a b c d p.x p.y hdet).symm)

@[simp] theorem sectionalCurvatureBilinPlane_mk {B : U → U → U → U → ℝ}
    (hB : IsAlgebraicCurvature B) (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hG : ∀ x y, G x y = G y x) (p : SectionalPlaneBasis U) :
    sectionalCurvatureBilinPlane hB G hG (sectionalPlaneMk p) =
      B p.x p.y p.x p.y / wedgePairingDiag G p.x p.y := by
  rfl

/-- Generator-independence of the tangent-compatible bilinear quotient. -/
theorem sectionalCurvatureBilinPlane_basis_independent {B : U → U → U → U → ℝ}
    (hB : IsAlgebraicCurvature B) (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (_hG : ∀ x y, G x y = G y x) {p q : SectionalPlaneBasis U}
    (hpq : sectionalPlaneChange p q) :
    B p.x p.y p.x p.y / wedgePairingDiag G p.x p.y =
      B q.x q.y q.x q.y / wedgePairingDiag G q.x q.y := by
  rcases hpq with ⟨a, b, c, d, hdet, hqx, hqy⟩
  rw [hqx, hqy]
  simpa [wedgePairingDiag] using
    (sectionalCurvatureBilin_changeBasis hB G a b c d p.x p.y hdet).symm

/-- The tangent-compatible descended evaluator is independent of the chosen
representative of an equal quotient plane. -/
theorem sectionalCurvatureBilinPlane_eq_of_eq {B : U → U → U → U → ℝ}
    (hB : IsAlgebraicCurvature B) (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hG : ∀ x y, G x y = G y x) {p q : SectionalPlaneBasis U}
    (h : sectionalPlaneMk p = sectionalPlaneMk q) :
    B p.x p.y p.x p.y / wedgePairingDiag G p.x p.y =
      B q.x q.y q.x q.y / wedgePairingDiag G q.x q.y := by
  simpa only [sectionalCurvatureBilinPlane_mk] using
    (congrArg (sectionalCurvatureBilinPlane hB G hG) h)

/-- The tangent-compatible evaluator is unchanged by swapping generators. -/
theorem sectionalCurvatureBilinPlane_swap {B : U → U → U → U → ℝ}
    (hB : IsAlgebraicCurvature B) (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hG : ∀ x y, G x y = G y x) (p : SectionalPlaneBasis U) :
    sectionalCurvatureBilinPlane hB G hG (sectionalPlaneMk p.swap) =
      sectionalCurvatureBilinPlane hB G hG (sectionalPlaneMk p) := by
  rw [sectionalPlaneMk_swap]

end Curvature
end Ch01
end MorganTianLib
