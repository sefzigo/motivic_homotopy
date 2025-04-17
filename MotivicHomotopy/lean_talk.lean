import Mathlib.MeasureTheory.Integral.Lebesgue.Basic  -- For integrals and measures
import Mathlib.MeasureTheory.Function.L1Space.Integrable  -- For integrals and measures
import Mathlib.Order.Filter.Basic              -- For liminf and atTop
import Mathlib.Order.Lattice                   -- For ⨅ (infimum)
import Mathlib.MeasureTheory.Function.L1Space.Integrable  -- For integrals and measures
import Mathlib.Data.NNReal.Defs


open MeasureTheory -- For integrals and measures
open ENNReal NNReal-- For extended non-negative reals
open Filter -- For liminf and atTop
open Topology -- For 𝓝 (neighborhoods)

variable {Ω: Type*} [MeasurableSpace Ω]
variable  {μ : Measure Ω}

noncomputable def fpos {α : Type*} (f : α → ℝ) : α → NNReal := fun x => (f x).toNNReal

noncomputable def fneg {α : Type*} (f : α → ℝ) : α → NNReal := fun x => (- f x).toNNReal

/-- The **Lebesgue integral** of a function real valued function `f` with respect to a measure `μ`. Only well-behaved for L1 functions-/
noncomputable irreducible_def Lintegral (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
(∫⁻ a, (f a).toNNReal ∂μ).toReal - (∫⁻ a, (-f a).toNNReal ∂μ).toReal

/-
Useful stuff for theorem proving:
- exact? searches for a single lemma that closed the goal using the current hypotheses
- apply? gives a list of lemmas that can apply to the current goal.
- rw? gives a list of lemmas that can be used to rewrite the current goal.
- have? using h1, h2 try to find facts that can be concluded by using both h1 and h2.
-- #min_imports gives a list of all the imports needed up to the current point.

Favourite tactics:
- hint: runs a few common tactics on the goal, reporting which one succeeded.
- aesop: simplifies the goal, and uses various tactics to prove it.
- #loogle query: Uses Lean search to find declarations that match the query.
- #leansearch query: Use Lean search to find declarations that match the query.



Key measure theory concepts in Lean:
- `∫⁻ a, f a ∂μ`: Lebesgue integral for ℝ≥0∞-valued functions.
  Example: `∫⁻ a, f n a ∂μ` integrates `f n` over `Ω`.
- `⨅ i, f i`: Infimum over an indexed family.
  Example: `⨅ i : {i : ℕ // i ≥ n}, f i a` takes inf over `i ≥ n`.
- `⨆ i, f i`: Supremum over an indexed family.
  Example: `⨆ n, g n a` takes sup over `n`.
- `{i : ℕ // i ≥ n}`: Subtype for indices `i ≥ n`.
  Example: `{i : ℕ // i ≥ n}` filters naturals.
- `liminf (fun n => f n) atTop`: Limit inferior as `n → ∞`.
  Example: `liminf (fun n => f n a) atTop` approximates `f`’s smallest limit.
- `∀ᵐ a ∂μ, P a`: Property `P a` holds almost everywhere.
  Example: `∀ᵐ a ∂μ, f a ≤ g a` means `f ≤ g` a.e.
- `Tendsto (fun n => x n) atTop (𝓝 y)`: Sequence `x n` converges to `y`.
  Example: `Tendsto (fun n => ∫⁻ a, f n a ∂μ) atTop (𝓝 (∫⁻ a, f_lim a ∂μ))`.

-/


theorem fatous_lemma {f : ℕ → Ω → ℝ≥0∞} (fn_meas : ∀ n, Measurable (f n)) :
∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop := by

-- Defining g(x) and f_lim(x)
  let g (n : ℕ) (a : Ω) : ℝ≥0∞ := ⨅ i : { i : ℕ // i ≥ n }, f i a -- g(n)(a) = inf { f(i)(a) | i ≥ n }
  let f_lim (a : Ω) : ℝ≥0∞ := liminf (fun n => f n a) atTop

-- Proving that g_n is measurable
  have gn_measurable : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.iInf -- Theorem: Infimum of a countable of measurable functions is measurable
    intro i
    exact fn_meas i

-- Proving that g_n is monotonic
  have gnx_mono : ∀ a n m, n ≤ m → g n a ≤ g m a := by
    intro a n m hnm
    simp only [g]                                                     -- rewriting with definition of g
    refine iInf_mono' (fun ⟨i, hi⟩ => ⟨⟨i, le_trans hnm hi⟩, le_rfl⟩)
    -- What this does is showing: inf_{k≥n} f k ≤ inf_{k≥m} f k  when n ≤ m
    -- So inf over smaller set

-- Proving gn less than or equal fi for all i ≥ n
  have gn_le_fi_allx : ∀ a n i, i ≥ n → g n a ≤ f i a := by
    intro a n i hi
    simp [g]
    apply iInf_le_of_le ⟨i, hi⟩  -- Theorem: iInf is less than or equal to any element in the set
    exact le_rfl                 -- exacting the reflexivity of ≤

-- Proving integral of g_n is less than or equal to integral of f_i
  have int_gn_le_int_fi_alligen : ∀ n i, i ≥ n → ∫⁻ a, g n a ∂μ ≤ ∫⁻ a, f i a ∂μ := by
    intro n i hi
    apply lintegral_mono          -- Theorem: If f ≤ g, then ∫ f ≤ ∫ g
    intro a
    exact gn_le_fi_allx a n i hi  -- previously proved that g n a ≤ f i a

  have integral_gn_le_inf_fi : ∀ n, ∫⁻ x, g n x ∂μ ≤ ⨅ i : {i : ℕ // i ≥ n}, ∫⁻ a, f i a ∂μ := by
    intro n
    apply le_iInf                  -- reduces prove to showing ∫⁻ g n x ≤ ∫⁻ a, f i a for some specific i
    intro i
    apply int_gn_le_int_fi_alligen -- Using previously proved lemma
    exact i.2                      -- i.2 accesses the condition i ≥ n in the subtype {i : ℕ // i ≥ n}


  calc
      ∫⁻ a, f_lim a ∂μ = ∫⁻ a, liminf (fun n => f n a) atTop ∂μ := by rfl  -- ∫ f_lim dμ = ∫ (liminf fₙ) dμ
      _ = ∫⁻ a, ⨆ n, g n a ∂μ := by
        congr; ext a
        rw [liminf_eq_iSup_iInf_of_nat]                       -- liminf fₙ(a) = supₙ inf_{i≥n} fᵢ(a)
        simp [g, iInf_subtype]
      _ = ⨆ n, ∫⁻ a, g n a ∂μ := by                           -- ∫ (supₙ gₙ) dμ = supₙ ∫ gₙ dμ
        refine lintegral_iSup (fun n => gn_measurable n) ?_   -- Here we use Montone Convergence Theorem i.e lintegral_iSup
        intro n m hnm a
        exact gnx_mono a n m hnm
      _ ≤ ⨆ n, ⨅ (i : ℕ) (hi : i ≥ n), ∫⁻ a, f i a ∂μ := by   -- ∫ gₙ dμ ≤ inf_{i≥n} ∫ fᵢ dμ
        refine iSup_mono (fun n => ?_)
        rw [iInf_subtype']
        exact integral_gn_le_inf_fi n
      _ = liminf (fun n => ∫⁻ a, f n a ∂μ) atTop := by        -- supₙ inf_{i≥n} ∫ fᵢ dμ
        simp only [liminf_eq_iSup_iInf_of_nat]



theorem dominated_convergence
    {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {g : Ω → ℝ≥0}
    (Fn_integ : ∀ n, Integrable (F n) μ)
    (g_integ : Integrable g μ)
    (Fn_bound : ∀ n a, |F n a| ≤ ↑(g a))
    (Fn_meas : ∀ n, Measurable (F n))
    (Fn_ptw_conv : Tendsto (fun n => F n ) atTop (𝓝 f)) :
    Integrable f μ ∧ Tendsto (fun n => Lintegral μ (F n)) atTop (𝓝 (Lintegral μ f)) := by

  -- Step 1: measurability of f
  have f_meas : Measurable f := measurable_of_tendsto_metrizable Fn_meas Fn_ptw_conv

  -- Step 2: use Fatou on f⁺ := (f x).toNNReal and f⁻ := (-f x).toNNReal
  set fpos := fun x => (f x).toNNReal
  set fneg := fun x => (-f x).toNNReal
  set fn_pos := fun n x => (F n x).toNNReal
  set fn_neg := fun n x => (-F n x).toNNReal

  -- measurability
  have meas_fn_pos : ∀ n, Measurable (fn_pos n) := fun n => measurable_toNNReal.comp (Fn_meas n)
  have meas_fn_neg : ∀ n, Measurable (fn_neg n) := fun n => measurable_toNNReal.comp ((Fn_meas n).neg)

  -- bounds: |F n x| ≤ g x ⇒ both fn_pos and fn_neg ≤ ↑g
  have bound_fn_pos : ∀ n x, fn_pos n x ≤ ↑(g x) := by
    intro n x; exact toNNReal_le_toNNReal (abs_nonneg _) (NNReal.coe_nonneg _) (Fn_bound n x)
  have bound_fn_neg : ∀ n x, fn_neg n x ≤ ↑(g x) := by
    intro n x; rw [abs_neg]; exact toNNReal_le_toNNReal (abs_nonneg _) (NNReal.coe_nonneg _) (Fn_bound n x)

  -- dominated ⇒ use Fatou on fpos
  have fpos_le_g : ∫⁻ x, fpos x ∂μ ≤ liminf (fun n => ∫⁻ x, fn_pos n x ∂μ) atTop := by
    apply fatous_lemma meas_fn_pos

  have fneg_le_g : ∫⁻ x, fneg x ∂μ ≤ liminf (fun n => ∫⁻ x, fn_neg n x ∂μ) atTop := by
    apply fatous_lemma meas_fn_neg

  -- upper bounds via g
  have bound_fn : ∀ n, ∫⁻ x, fn_pos n x ∂μ ≤ ∫⁻ x, ↑(g x) ∂μ := fun n =>
    lintegral_mono (bound_fn_pos n)
  have bound_fn_neg : ∀ n, ∫⁻ x, fn_neg n x ∂μ ≤ ∫⁻ x, ↑(g x) ∂μ := fun n =>
    lintegral_mono (bound_fn_neg n)

  have fpos_fin : (∫⁻ x, fpos x ∂μ) < ∞ :=
    lt_of_le_of_lt fpos_le_g (lt_of_le_of_lt (iSup_le bound_fn) g_integ.2)

  have fneg_fin : (∫⁻ x, fneg x ∂μ) < ∞ :=
    lt_of_le_of_lt fneg_le_g (lt_of_le_of_lt (iSup_le bound_fn_neg) g_integ.2)

  -- f ∈ L¹
  have f_integ : Integrable f μ := by
    rw [Integrable, Lintegrable]
    use f_meas
    simp [hasFiniteIntegral, fpos, fneg]
    exact ⟨fpos_fin.ne, fneg_fin.ne⟩

  -- Step 3: convergence of ∫ Fₙ to ∫ f
  have lim_int : Tendsto (fun n => Lintegral μ (F n)) atTop (𝓝 (Lintegral μ f)) := by
    unfold Lintegral
    simp only [fpos, fneg]
    apply tendsto.sub
    · apply tendsto_of_liminf_eq_limsup
      exact ⟨fatous_lemma meas_fn_pos, by
        apply ge_of_tendsto
        apply tendsto_lintegral_of_dominated_convergence (fun n x => fn_pos n x)
        all_goals
          try apply measurable_toNNReal.comp (Fn_meas _)
          exact measurable_toNNReal.comp (measurable_abs f_meas)
          exact g_integ.1
          intro x
          apply tendsto_toNNReal.comp (tendsto_abs (Fn_ptw x))
          exact eventually_of_forall (λ _ => true)⟩
    · apply tendsto_of_liminf_eq_limsup
      exact ⟨fatous_lemma meas_fn_neg, by
        apply ge_of_tendsto
        apply tendsto_lintegral_of_dominated_convergence (fun n x => fn_neg n x)
        all_goals
          try apply measurable_toNNReal.comp ((Fn_meas _).neg)
          exact measurable_toNNReal.comp (measurable_abs (measurable_neg f_meas))
          exact g_integ.1
          intro x
          simp only [Function.comp_apply]
          apply tendsto_toNNReal.comp (tendsto_abs.comp (tendsto_neg.comp (Fn_ptw x)))
          exact eventually_of_forall (λ _ => true)⟩

  exact ⟨f_integ, lim_int⟩




/-
theorem dominated_convergence {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {g : Ω → ℝ≥0}
(Fn_integ : ∀ n, Integrable (F n) μ)
(g_integ : Integrable g μ)
(Fn_bound : ∀ n a, |F n a| ≤ |(g a).toReal|)
(Fn_meas : ∀ n, Measurable (F n))
(Fn_ptw_conv_f : ∀ a, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : -- Fct. converges ptw. to f
Integrable f μ ∧ Tendsto (fun n => Lintegral μ (F n)) atTop (𝓝 (Lintegral μ f)) := by

  let f (a : Ω) : ℝ := limUnder atTop (fun n => F n a)

  have Fx_le_gx : ∀ n a, |F n a| ≤ g a := by
    intro n a
    simp_all only [NNReal.abs_eq]


  have fx_le_gx : ∀ a, |f a| ≤ g a := by
    intro a
    simp only [f]
    exact


  have f_abs_le_g : Lintegral μ (fun x => |f x|) ≤ (∫⁻ a, g a ∂μ).toReal := by
    unfold Lintegral
    simp only [abs_toNNReal, neg_abs, abs_nonneg, toNNReal_zero]
    rw [sub_zero]  -- Removes the subtracted term since (-|f x|).toNNReal = 0
    apply ENNReal.toReal_mono (ne_of_lt ?_) (lintegral_mono ?_)
    · -- Show ∫⁻ g ∂μ is finite
      exact g_integ.2
    · -- Show pointwise bound |f x| ≤ g x
      intro x
      rw [ENNReal.ofReal_le_iff_le_toReal (abs_nonneg (f x)) (NNReal.coe_nonneg (g x))]
      simp only [NNReal.coe_toReal]
      exact le_of_tendsto (tendsto_abs (Fn_ptw_conv_f x))
        (eventually_of_forall (fun n => Fn_bound n x))
-/
