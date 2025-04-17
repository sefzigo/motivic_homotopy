import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable  -- For integrals and measures
import Mathlib.Order.Filter.Basic              -- For liminf and atTop
import Mathlib.Order.Lattice                   -- For ⨅ (infimum)
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open MeasureTheory -- For integrals and measures
open Set ENNReal NNReal Real-- For extended non-negative reals
open Filter -- For liminf and atTop
open Topology -- For 𝓝 (neighborhoods)

variable {Ω: Type*} [MeasurableSpace Ω]
variable  {μ : Measure Ω}


example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp


#min_imports

/-- The **Lebesgue integral** of a function real valued function `f` with respect to a measure `μ`. Only well-behaved for L1 functions-/
@[simp]
noncomputable def Lintegral (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
(∫⁻ a, (f a).toNNReal ∂μ).toReal - (∫⁻ a, (-f a).toNNReal ∂μ).toReal


theorem Lintegral_monotone {f : Ω → ℝ} {μ : Measure Ω} (f_integ : Integrable f μ ) :
|Lintegral μ f| ≤ Lintegral μ |f| := by sorry

theorem Lintegral_add {f g : Ω → ℝ} {μ : Measure Ω} (f_integ : Integrable f μ ) (g_integ : Integrable g μ ): Lintegral μ (f + g) =  Lintegral μ f + Lintegral μ g := by sorry

theorem Lintegral_smul {f : Ω → ℝ} {μ : Measure Ω} (c : ℝ) (f_integ : Integrable f μ ):
Lintegral μ (fun x =>  c * (f x)) = c * (Lintegral μ f) := by sorry


theorem fatous_lemma {f : ℕ → Ω → ℝ≥0∞} (fn_meas : ∀ n, Measurable (f n)) :
∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop := by

-- Definitions of g and f_lim
  let g (n : ℕ) (a : Ω) : ℝ≥0∞ := ⨅ i : { i : ℕ // i ≥ n }, f i a -- Defining g
  let f_lim (a : Ω) : ℝ≥0∞ := liminf (fun n => f n a) atTop

  have gn_measurable : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.iInf
    intro i
    exact fn_meas i

  have gnx_mono : ∀ a n m, n ≤ m → g n a ≤ g m a := by
    intro a n m hnm
    simp only [g]
    refine iInf_mono' (fun i => ?_)
    let j : {i // n ≤ i} := ⟨i.val, le_trans hnm i.property⟩
    exact ⟨j, le_rfl⟩


  have gn_le_fi_allx : ∀ a n i, i ≥ n → g n a ≤ f i a := by
    intro a n i hi
    simp [g]
    apply iInf_le_of_le ⟨i, hi⟩
    exact le_rfl

  have int_gn_le_int_fi_alligen : ∀ n i, i ≥ n → ∫⁻ a, g n a ∂μ ≤ ∫⁻ a, f i a ∂μ := by
    intro n i hi
    apply lintegral_mono
    intro a
    exact gn_le_fi_allx a n i hi

  have integral_gn_le_inf_fi : ∀ n, ∫⁻ x, g n x ∂μ ≤ ⨅ i : {i : ℕ // i ≥ n}, ∫⁻ a, f i a ∂μ := by
    intro n
    apply le_iInf
    intro i
    apply int_gn_le_int_fi_alligen
    exact i.2


  calc
      ∫⁻ a, f_lim a ∂μ = ∫⁻ a, liminf (fun n => f n a) atTop ∂μ := by rfl
      _ = ∫⁻ a, ⨆ n, g n a ∂μ := by
        congr; ext a
        rw [liminf_eq_iSup_iInf_of_nat]
        simp [g, iInf_subtype]
      _ = ⨆ n, ∫⁻ a, g n a ∂μ := by
        refine lintegral_iSup (fun n => gn_measurable n) ?_
        intro n m hnm a
        exact gnx_mono a n m hnm
      _ ≤ ⨆ n, ⨅ (i : ℕ) (hi : i ≥ n), ∫⁻ a, f i a ∂μ := by
        refine iSup_mono (fun n => ?_)
        rw [iInf_subtype']
        exact integral_gn_le_inf_fi n
      _ = liminf (fun n => ∫⁻ a, f n a ∂μ) atTop := by
        simp only [liminf_eq_iSup_iInf_of_nat]




--variable {f : ℕ → Ω → ℝ} {f_lim : Ω → ℝ} put them into the arguments of the theorem

theorem dominated_convergence {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {g : Ω → ℝ}
  --(fn_meas : ∀ n, Measurable (f n)) not necessary because integrable includes measurable
  --(f_lim_meas : Measurable f_lim) follows from general theory.
  (Fn_integ : ∀ n, Integrable (F n) μ)
  (g_integ : Integrable g μ)
  (f_bound : ∀ n a, |F n a| ≤ |(g a)|)
  (Fn_ptw_conv_f : ∀ a, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
  Integrable f μ ∧  Tendsto (fun n => Lintegral μ (F n)) atTop (𝓝 (Lintegral μ f)) := by

  have hf_int : Integrable f μ := by
    refine' Integrable.mono' g_integ ?_ ?_
    · sorry
    · sorry


  constructor -- show that f is integrable, follows from standard results
  · exact hf_int

  --supplementary can probably be removed
  have hd_int : ∀ n : ℕ, Integrable ((F n) - f) μ := by sorry
  have hf_neg_int : Integrable (fun x ↦ -1 * f x) μ := by sorry

  -- main calculation
  have : ∫⁻ a, 2*(g a).toNNReal ∂μ ≤
   ∫⁻ a, 2*(g a).toNNReal ∂μ - limsup (fun n => ∫⁻ a, (|F n a - f a|).toNNReal ∂μ) atTop :=
    calc
      ∫⁻ a, 2*(g a).toNNReal ∂μ = ∫⁻ a, liminf (fun n => 2*(g a).toNNReal -(|F n a - f a|).toNNReal) atTop ∂μ := by sorry
      _ ≤ liminf (fun n => ∫⁻ a, (2*(g a).toNNReal -(|F n a - f a|).toNNReal) ∂μ) atTop := by sorry
      _ = liminf (fun n => ∫⁻ a, 2*(g a).toNNReal ∂μ - ∫⁻ a, (|F n a - f a|).toNNReal ∂μ) atTop := by sorry
      _ = ∫⁻ a, 2*(g a).toNNReal ∂μ - limsup (fun n => ∫⁻ a, (|F n a - f a|).toNNReal ∂μ) atTop := by sorry

  -- extract limsup = 0, follows from lemma on <
  have h0 : limsup (fun n ↦ (∫⁻ (a : Ω), ↑(nnabs (F n a - f a)) ∂μ).toReal) atTop = 0 := by sorry

  -- used to simplify the .toNNReal later
  have hneg : ∀ n : ℕ, ∀ x : Ω, -|F n x - f x| ≤ 0 := by sorry

  -- deduce that integral of difference converges to 0
  have h_diff : Tendsto (fun n => Lintegral μ (fun x => |F n x - f x| )) atTop (𝓝 0) := by
    simp [toNNReal_eq_zero.mpr (hneg _ _)]
    refine' tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
    · sorry
    · norm_num [h0]
    · sorry
    · use 0
      norm_num

  -- integral bounded -> could be a general lemma about Lintegral
  have h_bound: ∀ n :ℕ , ‖‖Lintegral μ (F n) - Lintegral μ f‖‖ ≤ Lintegral μ |((F n) - f)| := by
    intro n
    rw[sub_eq_add_neg]
    rw[neg_eq_neg_one_mul]
    rw[← Lintegral_smul (-1) hf_int]
    rw[← Lintegral_add (Fn_integ n) hf_neg_int]
    simp [-Lintegral]
    exact Lintegral_monotone (hd_int n)

  -- final steps
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm h_bound
  exact h_diff
