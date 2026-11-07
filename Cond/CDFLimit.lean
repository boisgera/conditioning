import Mathlib

/-!
# The conditional CDF as a limit of elementary conditional probabilities

Formalisation of `notes/conditional-cdf-as-a-limit.md`.

Distances on `[-∞, ∞]` are measured through an arbitrary measurable embedding
`φ : EReal → ℝ`, via `d(s, t) = |φ s - φ t|` (the note uses
`φ t = t / (1 + |t|)`). The elementary conditional CDF is
`approxCDF φ X Y y x ε = P(X ≤ x, d(Y, y) ≤ ε) / P(d(Y, y) ≤ ε)`, and the
conditional CDF is `condDistrib X Y volume y (Iic x)`.

* `ae_tendsto_approxCDF`: part 1 of the theorem (fixed `x`, a.e. `y`).
* `ae_forall_tendsto_approxCDF`: part 2 (a.e. `y`, all rational `x`, `±∞`, and
  all continuity points of the conditional CDF).
* `tendsto_approxCDF_of_atom`, `condDistrib_Iic_of_atom`: part 3 (atoms).
-/

open MeasureTheory ProbabilityTheory unitInterval Filter Topology Set Metric
open scoped ENNReal

namespace CDFLimit

/-- The elementary conditional CDF `P(X ≤ x, d(Y, y) ≤ ε) / P(d(Y, y) ≤ ε)`,
where `d(s, t) = |φ s - φ t|`. -/
noncomputable def approxCDF (φ : EReal → ℝ) (X Y : I → EReal) (y x : EReal) (ε : ℝ) : ℝ≥0∞ :=
  volume {u | X u ≤ x ∧ |φ (Y u) - φ y| ≤ ε} / volume {u | |φ (Y u) - φ y| ≤ ε}

variable {φ : EReal → ℝ} {X Y : I → EReal}

lemma approxCDF_mono (y : EReal) {x x' : EReal} (hx : x ≤ x') (ε : ℝ) :
    approxCDF φ X Y y x ε ≤ approxCDF φ X Y y x' ε := by
  refine ENNReal.div_le_div_right (measure_mono ?_) _
  intro u hu
  exact ⟨hu.1.trans hx, hu.2⟩

/-- The denominator, as the measure of a ball for the law of `φ ∘ Y`. -/
lemma volume_dist_le (hY : AEMeasurable Y) (hφ : MeasurableEmbedding φ) (y : EReal) (ε : ℝ) :
    volume {u | |φ (Y u) - φ y| ≤ ε} = ((volume.map Y).map φ) (closedBall (φ y) ε) := by
  rw [Measure.map_apply hφ.measurable measurableSet_closedBall,
    Measure.map_apply_of_aemeasurable hY (hφ.measurable measurableSet_closedBall)]
  rfl

/-- The numerator, as the measure of a ball for the image by `φ` of the measure
`P_Y` with density `y ↦ κ(y)([-∞, x])`. -/
lemma volume_le_dist_le (hX : AEMeasurable X) (hY : AEMeasurable Y) (hφ : MeasurableEmbedding φ)
    (y x : EReal) (ε : ℝ) :
    volume {u | X u ≤ x ∧ |φ (Y u) - φ y| ≤ ε} =
      (((volume.map Y).withDensity fun y ↦ condDistrib X Y volume y (Iic x)).map φ)
        (closedBall (φ y) ε) := by
  have hS : MeasurableSet (φ ⁻¹' closedBall (φ y) ε) := hφ.measurable measurableSet_closedBall
  rw [Measure.map_apply hφ.measurable measurableSet_closedBall, withDensity_apply _ hS,
    ← Measure.compProd_apply_prod hS measurableSet_Iic, compProd_map_condDistrib hY hX,
    Measure.map_apply_of_aemeasurable (hY.prodMk hX) (hS.prod measurableSet_Iic)]
  congr 1
  ext u
  simp [Real.dist_eq, and_comm]

lemma approxCDF_eq (hX : AEMeasurable X) (hY : AEMeasurable Y) (hφ : MeasurableEmbedding φ)
    (y x : EReal) :
    approxCDF φ X Y y x = fun ε ↦
      (((volume.map Y).withDensity fun y ↦ condDistrib X Y volume y (Iic x)).map φ)
        (closedBall (φ y) ε) / ((volume.map Y).map φ) (closedBall (φ y) ε) := by
  ext ε
  rw [approxCDF, volume_le_dist_le hX hY hφ, volume_dist_le hY hφ]

lemma isFiniteMeasure_withDensity_condDistrib (x : EReal) :
    IsFiniteMeasure ((volume.map Y).withDensity fun y ↦ condDistrib X Y volume y (Iic x)) := by
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  calc ∫⁻ y, condDistrib X Y volume y (Iic x) ∂(volume.map Y)
      ≤ ∫⁻ _, 1 ∂(volume.map Y) := lintegral_mono fun _ ↦ prob_le_one
    _ < ∞ := by simp

/-- **Part 1.** For every `x` and `P_Y`-almost every `y`, the events `d(Y, y) ≤ ε`
have positive probability, and `P(X ≤ x | d(Y, y) ≤ ε) → κ(y)([-∞, x])`. -/
theorem ae_tendsto_approxCDF (hX : AEMeasurable X) (hY : AEMeasurable Y)
    (hφ : MeasurableEmbedding φ) (x : EReal) :
    ∀ᵐ y ∂(volume.map Y), (∀ ε > 0, volume {u | |φ (Y u) - φ y| ≤ ε} ≠ 0) ∧
      Tendsto (approxCDF φ X Y y x) (𝓝[>] 0) (𝓝 (condDistrib X Y volume y (Iic x))) := by
  set ν := volume.map Y
  set G : EReal → ℝ≥0∞ := fun y ↦ condDistrib X Y volume y (Iic x)
  have hG : Measurable G := (condDistrib X Y volume).measurable_coe measurableSet_Iic
  set ρ := ν.withDensity G
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_condDistrib x
  have h1 := hφ.ae_map_iff.mp (Besicovitch.ae_tendsto_rnDeriv (ρ.map φ) (ν.map φ))
  have h2 := hφ.ae_map_iff.mp (Besicovitch.ae_tendsto_rnDeriv (ν.map φ) (ν.map φ))
  have h3 := hφ.ae_map_iff.mp (Measure.rnDeriv_self (ν.map φ))
  filter_upwards [h1, h2, h3, hφ.rnDeriv_map ρ ν, Measure.rnDeriv_withDensity ν hG]
    with y hy1 hy2 hy3 hy4 hy5
  refine ⟨fun ε hε h0 ↦ ?_, ?_⟩
  · -- if a ball has measure zero, the ratio `ν / ν` is eventually `0`, not `1`
    rw [volume_dist_le hY hφ] at h0
    have h0' : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (ν.map φ) (closedBall (φ y) r) / (ν.map φ) (closedBall (φ y) r) = 0 := by
      filter_upwards [Ioo_mem_nhdsGT hε] with r hr
      have : (ν.map φ) (closedBall (φ y) r) = 0 :=
        measure_mono_null (closedBall_subset_closedBall hr.2.le) h0
      simp [this]
    have := tendsto_nhds_unique hy2 (tendsto_const_nhds.congr' (EventuallyEq.symm h0'))
    rw [hy3] at this
    simp at this
  · have e : condDistrib X Y volume y (Iic x) = (ρ.map φ).rnDeriv (ν.map φ) (φ y) := by
      rw [hy4, hy5]
    rw [approxCDF_eq hX hY hφ, e]
    exact hy1

/-- **Part 2.** For `P_Y`-almost every `y`, `P(X ≤ x | d(Y, y) ≤ ε) → κ(y)([-∞, x])`
simultaneously for all rational `x`, for `x = ±∞`, and for every `x` at which the
conditional CDF `κ(y)([-∞, ·])` is continuous. -/
theorem ae_forall_tendsto_approxCDF (hX : AEMeasurable X) (hY : AEMeasurable Y)
    (hφ : MeasurableEmbedding φ) :
    ∀ᵐ y ∂(volume.map Y), ∀ x : EReal,
      (x = ⊥ ∨ x = ⊤ ∨ (∃ q : ℚ, x = ((q : ℝ) : EReal)) ∨
        ContinuousAt (fun x ↦ condDistrib X Y volume y (Iic x)) x) →
      Tendsto (approxCDF φ X Y y x) (𝓝[>] 0) (𝓝 (condDistrib X Y volume y (Iic x))) := by
  have hQ : ∀ᵐ y ∂(volume.map Y), ∀ q : ℚ, Tendsto (approxCDF φ X Y y ((q : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 (condDistrib X Y volume y (Iic ((q : ℝ) : EReal)))) :=
    ae_all_iff.mpr fun q ↦ (ae_tendsto_approxCDF hX hY hφ _).mono fun _ h ↦ h.2
  filter_upwards [hQ, ae_tendsto_approxCDF hX hY hφ ⊥, ae_tendsto_approxCDF hX hY hφ ⊤]
    with y hyQ hybot hytop
  set G : EReal → ℝ≥0∞ := fun x ↦ condDistrib X Y volume y (Iic x)
  rintro x (rfl | rfl | ⟨q, rfl⟩ | hx)
  · exact hybot.2
  · exact hytop.2
  · exact hyQ q
  -- `x` is a continuity point: squeeze between rationals
  rcases eq_bot_or_bot_lt x with rfl | hxbot
  · exact hybot.2
  rcases eq_top_or_lt_top x with rfl | hxtop
  · exact hytop.2
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨l, hlx, hl⟩ := exists_Ioc_subset_of_mem_nhds
      (hx.eventually (lt_mem_nhds ha)) ⟨⊥, hxbot⟩
    obtain ⟨q, hlq, hqx⟩ := EReal.exists_rat_btwn_of_lt hlx
    have haq : a < G ((q : ℝ) : EReal) := hl ⟨hlq, hqx.le⟩
    filter_upwards [(tendsto_order.1 (hyQ q)).1 a haq] with ε hε
    exact hε.trans_le (approxCDF_mono y hqx.le ε)
  · obtain ⟨l, hxl, hl⟩ := exists_Ico_subset_of_mem_nhds
      (hx.eventually (gt_mem_nhds hb)) ⟨⊤, hxtop⟩
    obtain ⟨q, hxq, hql⟩ := EReal.exists_rat_btwn_of_lt hxl
    have hbq : G ((q : ℝ) : EReal) < b := hl ⟨hxq.le, hql⟩
    filter_upwards [(tendsto_order.1 (hyQ q)).2 b hbq] with ε hε
    exact (approxCDF_mono y hxq.le ε).trans_lt hε

/-- **Part 3.** At an atom `y` of the law of `Y`, `P(X ≤ x | d(Y, y) ≤ ε) → κ(y)([-∞, x])`
for every `x`, with no exceptional set. -/
theorem tendsto_approxCDF_of_atom (hX : AEMeasurable X) (hY : AEMeasurable Y)
    (hφ : MeasurableEmbedding φ) {y : EReal} (hy : volume.map Y {y} ≠ 0) (x : EReal) :
    Tendsto (approxCDF φ X Y y x) (𝓝[>] 0) (𝓝 (condDistrib X Y volume y (Iic x))) := by
  set ν := volume.map Y
  set G : EReal → ℝ≥0∞ := fun y ↦ condDistrib X Y volume y (Iic x)
  set ρ := ν.withDensity G
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_condDistrib x
  -- balls shrink to `{φ y}`, whose preimage under `φ` is `{y}`
  have hball : ∀ μ : Measure EReal, IsFiniteMeasure μ →
      Tendsto (fun ε ↦ (μ.map φ) (closedBall (φ y) ε)) (𝓝[>] 0) (𝓝 (μ {y})) := by
    intro μ _
    have h := tendsto_measure_biInter_gt (μ := μ.map φ) (s := fun r ↦ closedBall (φ y) r)
      (a := (0 : ℝ)) (fun _ _ ↦ measurableSet_closedBall.nullMeasurableSet)
      (fun _ _ _ hij ↦ closedBall_subset_closedBall hij) ⟨1, one_pos, measure_ne_top _ _⟩
    rw [biInter_gt_closedBall, closedBall_zero,
      Measure.map_apply hφ.measurable (measurableSet_singleton _)] at h
    have hpre : φ ⁻¹' {φ y} = {y} := by
      ext z; simp [hφ.injective.eq_iff]
    rwa [hpre] at h
  have hρ : ρ {y} = G y * ν {y} := by
    rw [withDensity_apply _ (measurableSet_singleton y), lintegral_singleton]
  rw [approxCDF_eq hX hY hφ]
  have := ENNReal.Tendsto.div (hball ρ inferInstance) (Or.inr hy) (hball ν inferInstance)
    (Or.inl (measure_ne_top _ _))
  rwa [hρ, ENNReal.mul_div_cancel_right hy (measure_ne_top _ _)] at this

/-- At an atom `y` of the law of `Y`, the conditional CDF is given by the elementary
formula `P(X ≤ x, Y = y) / P(Y = y)`. -/
theorem condDistrib_Iic_of_atom (hX : AEMeasurable X) (hY : AEMeasurable Y) {y : EReal}
    (hy : volume.map Y {y} ≠ 0) (x : EReal) :
    condDistrib X Y volume y (Iic x) =
      volume {u | X u ≤ x ∧ Y u = y} / volume {u | Y u = y} := by
  have hnum : volume {u | X u ≤ x ∧ Y u = y} =
      condDistrib X Y volume y (Iic x) * volume.map Y {y} := by
    have h := lintegral_singleton (μ := volume.map Y) (fun y ↦ condDistrib X Y volume y (Iic x)) y
    rw [← h, ← Measure.compProd_apply_prod (measurableSet_singleton y)
      measurableSet_Iic, compProd_map_condDistrib hY hX, Measure.map_apply_of_aemeasurable
      (hY.prodMk hX) ((measurableSet_singleton y).prod measurableSet_Iic)]
    congr 1
    ext u
    simp [and_comm]
  have hden : volume {u | Y u = y} = volume.map Y {y} := by
    rw [Measure.map_apply_of_aemeasurable hY (measurableSet_singleton y)]
    rfl
  rw [hnum, hden, ENNReal.mul_div_cancel_right hy (measure_ne_top _ _)]

end CDFLimit
