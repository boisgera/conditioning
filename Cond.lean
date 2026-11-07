import Mathlib
import Cond.CDFLimit

/-!
Original statement:

Given two Lebesgue-Borel measurable functions X and Y from [0, 1] to
[-∞, ∞], there is a function denoted X|Y : [-∞, ∞] × [0, 1] → [-∞, ∞]
such that if $X$ is integrable, for any $y ∈ [-∞, +∞]$,
 1. for any $y ∈ [-∞, ∞]$, $(X|Y)(y, ·)$ is integrable,
 2. the function $u ∈ [0, 1] ↦ ∫ (X|Y) (Y(u), v) \, dv$ integrable,
 3. we have $∫ X = ∫ [∫ (X|Y) (Y(u), v) \, dv]$.
-/

/-!
Revised statement:

Let $λ$ denote the Lebesgue measure on $[0, 1]$.

Given two Lebesgue-Borel measurable functions $X$ and $Y$ from $[0, 1]$ to
$[-∞, ∞]$, there is a function denoted $X|Y : [-∞, ∞] × [0, 1] → [-∞, ∞]$
such that:

 0. $X|Y$ is (jointly) Borel measurable;
 1. under $λ ⊗ λ$, the function $(u, v) ↦ (Y(u), (X|Y)(Y(u), v))$ has the
    same law as $(Y, X)$ under $λ$. In other words, for almost every $y$
    with respect to the law of $Y$, the law of $(X|Y)(y, ·)$ under $λ$ is
    the conditional law of $X$ given $Y = y$.

Moreover, if $X$ is integrable, $X|Y$ can be chosen so that:

 2. for any $y ∈ [-∞, ∞]$, $(X|Y)(y, ·)$ is integrable;
 3. the function $u ∈ [0, 1] ↦ ∫ (X|Y)(Y(u), v) \, dv$ is integrable;
 4. we have $∫ X(u) \, du = ∫ [∫ (X|Y)(Y(u), v) \, dv] \, du$.
-/

/-!
Proof sketch (of the revised statement, as formalised below):

 * Conditional distribution. Let $μ$ be the law of $(Y, X)$ on
   $[-∞, ∞] × [-∞, ∞]$ and $P_Y$ its first marginal. Since $[-∞, ∞]$ is
   Polish, hence standard Borel, $μ = P_Y ⊗ κ$ for some Markov kernel $κ$
   from $[-∞, ∞]$ to $[-∞, ∞]$: $κ(y)$ is the conditional law of $X$ given
   $Y = y$ (`condDistrib X Y volume`, `compProd_map_condDistrib`).

 * Representation of the kernel. Any Markov kernel into a standard Borel
   space is the image of $λ$ by a jointly measurable map
   (`Kernel.exists_measurable_map_eq_unitInterval`, Kallenberg Lemma 4.22):
   there is a measurable $f : [-∞, ∞] × [0, 1] → [-∞, ∞]$ such that, for
   every $y$, the law of $f(y, ·)$ under $λ$ is $κ(y)$.

 * Law lemma (`map_eq_compProd`). If $Ψ$ is measurable and, for $P_Y$-almost
   every $y$, the law of $Ψ(y, ·)$ under $λ$ is $κ(y)$, then by Tonelli the
   law of $(u, v) ↦ (Y(u), Ψ(Y(u), v))$ under $λ ⊗ λ$ is
   $∫ δ_{Y(u)} ⊗ κ(Y(u)) \, du = P_Y ⊗ κ = μ$. This gives condition 1.

 * If $X$ is not integrable, take $X|Y := f$: conditions 0 and 1 hold and
   there is nothing more to prove.

 * If $X$ is integrable, let $F(x) = |x|$ for $x$ finite, $F(±∞) = ∞$, and
   $G(y) = ∫ F \, dκ(y)$. Then $∫ G \, dP_Y = ∫ F \, dμ(·, x) = ∫ F(X) < ∞$,
   so $G < ∞$ $P_Y$-almost everywhere. Set $(X|Y)(y, v) := 0$ if
   $G(y) = ∞$ and $(X|Y)(y, v) := f(y, v)$ otherwise.
   - Conditions 0 and 1 still hold, by the law lemma, since $X|Y$ only
     differs from $f$ on a $P_Y$-null set of $y$.
   - Condition 2: if $G(y) = ∞$ the section is $0$; otherwise
     $∫ F(f(y, v)) \, dv = G(y) < ∞$, so $f(y, ·)$ is finite almost
     everywhere and integrable.
   - Conditions 3 and 4: by condition 1, the function
     $(u, v) ↦ (X|Y)(Y(u), v)$ on $[0, 1]^2$ has the same law as $X$, hence
     is integrable with the same integral; conclude by Fubini.
-/

open MeasureTheory ProbabilityTheory unitInterval

/-- If every section `Ψ (y, ·)` has law `κ y` (for `P_Y`-almost every `y`), then
`(u, v) ↦ (Y u, Ψ (Y u, v))` has law `P_Y ⊗ κ` under `λ ⊗ λ` (case `Y` measurable). -/
lemma map_eq_compProd_of_measurable {Y : I → EReal} (hY : Measurable Y)
    (κ : Kernel EReal EReal) [IsMarkovKernel κ] {Ψ : EReal × I → EReal} (hΨ : Measurable Ψ)
    (hΨκ : ∀ᵐ y ∂(volume.map Y), volume.map (fun v ↦ Ψ (y, v)) = κ y) :
    (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Ψ (Y p.1, p.2))) =
      (volume.map Y) ⊗ₘ κ := by
  have hT : Measurable (fun p : I × I ↦ (Y p.1, Ψ (Y p.1, p.2))) := by fun_prop
  have hae : ∀ᵐ u ∂(volume : Measure I), volume.map (fun v ↦ Ψ (Y u, v)) = κ (Y u) :=
    ae_of_ae_map hY.aemeasurable hΨκ
  ext s hs
  rw [Measure.map_apply hT hs, Measure.compProd_apply hs,
    lintegral_map (κ.measurable_kernel_prodMk_left hs) hY, Measure.volume_eq_prod,
    Measure.prod_apply (hT hs)]
  refine lintegral_congr_ae (hae.mono fun u hu ↦ ?_)
  simp only
  rw [← hu, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

/-- Same as `map_eq_compProd_of_measurable`, for `Y` only almost everywhere measurable. -/
lemma map_eq_compProd {Y : I → EReal} (hY : AEMeasurable Y)
    (κ : Kernel EReal EReal) [IsMarkovKernel κ] {Ψ : EReal × I → EReal} (hΨ : Measurable Ψ)
    (hΨκ : ∀ᵐ y ∂(volume.map Y), volume.map (fun v ↦ Ψ (y, v)) = κ y) :
    (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Ψ (Y p.1, p.2))) =
      (volume.map Y) ⊗ₘ κ := by
  have hmap : (volume : Measure I).map Y = volume.map (hY.mk Y) :=
    Measure.map_congr hY.ae_eq_mk
  have hfst : ∀ᵐ p ∂(volume : Measure (I × I)), Y p.1 = hY.mk Y p.1 := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_fst.quasiMeasurePreserving).ae hY.ae_eq_mk
  rw [Measure.map_congr (g := fun p : I × I ↦ (hY.mk Y p.1, Ψ (hY.mk Y p.1, p.2)))
    (hfst.mono fun p hp ↦ by simp only [hp]), hmap]
  rw [hmap] at hΨκ
  exact map_eq_compProd_of_measurable hY.measurable_mk κ hΨ hΨκ

/-- Integrability of an extended-real-valued function: it is almost everywhere
finite and its real part is (Bochner) integrable. This matches the classical
notion `∫ |f| < ∞`. -/
def IntegrableEReal {α : Type*} [MeasurableSpace α] (f : α → EReal) (μ : Measure α) :
    Prop :=
  (∀ᵐ x ∂μ, f x ≠ ⊥ ∧ f x ≠ ⊤) ∧ Integrable (fun x ↦ (f x).toReal) μ

/-- `|x|` for `x` finite, `∞` for `x = ±∞`: `f` is `IntegrableEReal` iff
`∫⁻ extNorm ∘ f < ∞`. -/
noncomputable def extNorm (x : EReal) : ENNReal := if x = ⊤ ∨ x = ⊥ then ⊤ else ‖x.toReal‖ₑ

lemma measurable_extNorm : Measurable extNorm :=
  Measurable.ite ((measurableSet_singleton ⊤).union (measurableSet_singleton ⊥))
    measurable_const measurable_ereal_toReal.enorm

lemma enorm_toReal_le_extNorm (x : EReal) : ‖x.toReal‖ₑ ≤ extNorm x := by
  simp only [extNorm]; split_ifs <;> simp

lemma integrableEReal_of_lintegral_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → EReal} (hf : Measurable f) (h : ∫⁻ a, extNorm (f a) ∂μ < ⊤) :
    IntegrableEReal f μ := by
  refine ⟨(ae_lt_top (measurable_extNorm.comp hf) h.ne).mono fun a ha ↦ ?_, ?_⟩
  · by_contra hfa
    have h' : f a = ⊤ ∨ f a = ⊥ := by tauto
    have : extNorm (f a) = ⊤ := by simp only [extNorm, h', ite_true]
    exact ha.ne this
  · exact ⟨(measurable_ereal_toReal.comp hf).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr
        ((lintegral_mono fun a ↦ enorm_toReal_le_extNorm _).trans_lt h)⟩

lemma lintegral_extNorm_lt_top {X : I → EReal} (hXi : IntegrableEReal X volume) :
    ∫⁻ u, extNorm (X u) < ⊤ := by
  have hae : ∀ᵐ u ∂(volume : Measure I), extNorm (X u) = ‖(X u).toReal‖ₑ :=
    hXi.1.mono fun u hu ↦ by simp [extNorm, hu.1, hu.2]
  rw [lintegral_congr_ae hae]
  exact hasFiniteIntegral_iff_enorm.mp hXi.2.2

/-- If `X` is integrable, then the conditional law `κ(y)` is integrable (and
finite a.s.) for `P_Y`-almost every `y`. -/
lemma ae_lintegral_condDistrib_lt_top {X Y : I → EReal} (hX : AEMeasurable X)
    (hY : AEMeasurable Y) (hXi : IntegrableEReal X volume) :
    ∀ᵐ y ∂(volume.map Y), ∫⁻ x, extNorm x ∂(condDistrib X Y volume y) < ⊤ := by
  refine ae_lt_top measurable_extNorm.lintegral_kernel ?_
  have h := Measure.lintegral_compProd (μ := volume.map Y) (κ := condDistrib X Y volume)
    (measurable_extNorm.comp measurable_snd)
  simp only [Function.comp_apply] at h
  rw [← h, compProd_map_condDistrib hY hX, lintegral_map' (f := fun q : EReal × EReal ↦ extNorm q.2)
    (measurable_extNorm.comp measurable_snd).aemeasurable (hY.prodMk hX)]
  exact (lintegral_extNorm_lt_top hXi).ne

/-- Fubini for any `Ψ` reproducing the law of `(Y, X)`: conditions 3 and 4. -/
lemma integrable_and_integral_eq_of_map_eq {X Y : I → EReal} (hX : AEMeasurable X)
    (hY : AEMeasurable Y) {Ψ : EReal × I → EReal} (hΨ : Measurable Ψ)
    (hΨlaw : (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Ψ (Y p.1, p.2))) =
      (volume : Measure I).map (fun u ↦ (Y u, X u)))
    (hXi : IntegrableEReal X volume) :
    Integrable (fun u ↦ ∫ v, (Ψ (Y u, v)).toReal) ∧
      ∫ u, (X u).toReal = ∫ u, ∫ v, (Ψ (Y u, v)).toReal := by
  have hYfst : AEMeasurable (fun p : I × I ↦ Y p.1) volume := by
    rw [Measure.volume_eq_prod]
    exact hY.comp_quasiMeasurePreserving (measurePreserving_fst.quasiMeasurePreserving)
  have hk : Measurable (fun q : EReal × EReal ↦ q.2.toReal) :=
    measurable_ereal_toReal.comp measurable_snd
  have hT : AEMeasurable (fun p : I × I ↦ (Y p.1, Ψ (Y p.1, p.2))) volume :=
    hYfst.prodMk (hΨ.comp_aemeasurable (hYfst.prodMk measurable_snd.aemeasurable))
  have hYX : AEMeasurable (fun u ↦ (Y u, X u)) volume := hY.prodMk hX
  have h1 : Integrable (fun q : EReal × EReal ↦ q.2.toReal) (volume.map (fun u ↦ (Y u, X u))) :=
    (integrable_map_measure hk.aestronglyMeasurable hYX).mpr hXi.2
  rw [← hΨlaw] at h1
  have h2 : Integrable (fun p : I × I ↦ (Ψ (Y p.1, p.2)).toReal) (volume.prod volume) :=
    (integrable_map_measure hk.aestronglyMeasurable hT).mp h1
  refine ⟨h2.integral_prod_left, ?_⟩
  rw [← integral_prod _ h2, ← Measure.volume_eq_prod]
  calc ∫ u, (X u).toReal
      = ∫ q, q.2.toReal ∂(volume.map (fun u ↦ (Y u, X u))) :=
        (integral_map hYX hk.aestronglyMeasurable).symm
    _ = ∫ q, q.2.toReal ∂((volume : Measure (I × I)).map
          (fun p ↦ (Y p.1, Ψ (Y p.1, p.2)))) := by rw [hΨlaw]
    _ = _ := integral_map hT hk.aestronglyMeasurable

/-- Formal version of the revised statement. `Φ` plays the role of `X|Y`.
"Lebesgue-Borel measurable" is rendered as `AEMeasurable` (with respect to
the Lebesgue measure `volume` on `I = [0, 1]`); integrals of extended-real
functions are taken of their real parts, which is harmless for a.e. finite
functions.

Proof: `Φ` is built from the conditional distribution `condDistrib X Y volume`
with `Kernel.exists_measurable_map_eq_unitInterval` (a jointly measurable
representation of a Markov kernel by Lebesgue measure on `I`), then set to `0`
on the `P_Y`-null set of `y` where the conditional law is not integrable. -/
theorem exists_cond (X Y : I → EReal) (hX : AEMeasurable X) (hY : AEMeasurable Y) :
    ∃ Φ : EReal × I → EReal,
      -- 0. joint measurability
      Measurable Φ ∧
      -- 1. `(u, v) ↦ (Y u, Φ (Y u, v))` under `λ ⊗ λ` has the law of `(Y, X)` under `λ`
      (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Φ (Y p.1, p.2))) =
        (volume : Measure I).map (fun u ↦ (Y u, X u)) ∧
      (IntegrableEReal X volume →
        -- 2. every section is integrable
        (∀ y, IntegrableEReal (fun v ↦ Φ (y, v)) volume) ∧
        -- 3. the inner integral is integrable
        Integrable (fun u ↦ ∫ v, (Φ (Y u, v)).toReal) ∧
        -- 4. tower property
        ∫ u, (X u).toReal = ∫ u, ∫ v, (Φ (Y u, v)).toReal) := by
  set κ := condDistrib X Y volume
  obtain ⟨f, hf, hfκ⟩ := κ.exists_measurable_map_eq_unitInterval
  have hlaw : ∀ Ψ : EReal × I → EReal, Measurable Ψ →
      (∀ᵐ y ∂(volume.map Y), volume.map (fun v ↦ Ψ (y, v)) = κ y) →
      (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Ψ (Y p.1, p.2))) =
        (volume : Measure I).map (fun u ↦ (Y u, X u)) := fun Ψ hΨ h ↦
    (map_eq_compProd hY κ hΨ h).trans (compProd_map_condDistrib hY hX)
  by_cases hXi : IntegrableEReal X volume
  swap
  · exact ⟨Function.uncurry f, hf, hlaw _ hf (Filter.Eventually.of_forall fun y ↦ hfκ y),
      fun h ↦ absurd h hXi⟩
  -- set `Φ (y, ·) = 0` where `κ y` is not integrable
  let G : EReal → ENNReal := fun y ↦ ∫⁻ x, extNorm x ∂κ y
  have hG : Measurable G := measurable_extNorm.lintegral_kernel
  let Ψ : EReal × I → EReal := fun p ↦ if G p.1 = ⊤ then 0 else f p.1 p.2
  have hΨ : Measurable Ψ :=
    Measurable.ite ((hG.comp measurable_fst) (measurableSet_singleton ⊤)) measurable_const hf
  have hΨlaw := hlaw Ψ hΨ ((ae_lintegral_condDistrib_lt_top hX hY hXi).mono fun y hy ↦ by
    have hy' : G y ≠ ⊤ := hy.ne
    simp only [Ψ, hy', ite_false]
    exact hfκ y)
  refine ⟨Ψ, hΨ, hΨlaw, fun _ ↦
    ⟨fun y ↦ ?_, integrable_and_integral_eq_of_map_eq hX hY hΨ hΨlaw hXi⟩⟩
  by_cases hy : G y = ⊤
  · simp only [Ψ, hy]
    exact ⟨Filter.Eventually.of_forall fun _ ↦ by simp, by simp⟩
  · simp only [Ψ, hy, ite_false]
    refine integrableEReal_of_lintegral_lt_top hf.of_uncurry_left ?_
    rw [← lintegral_map measurable_extNorm hf.of_uncurry_left, hfκ y]
    exact lt_top_iff_ne_top.mpr hy

/-!
### An explicit choice: the conditional quantile function

Informal statement. Let $F(y, x) = κ(y)([-∞, x])$ be the conditional CDF of $X$
given $Y = y$ (here $κ$ is `condDistrib X Y volume`) and define
$$(X|Y)(y, v) = \inf \{x ∈ [-∞, ∞] \mid v ≤ F(y, x)\}.$$
Then:

 0. $X|Y$ is jointly Borel measurable, and nondecreasing in $v$;
 1. for every $y$, the law of $(X|Y)(y, ·)$ under $λ$ is $κ(y)$; hence
    $(u, v) ↦ (Y(u), (X|Y)(Y(u), v))$ under $λ ⊗ λ$ has the law of $(Y, X)$.

Moreover, if $X$ is integrable:

 2. for almost every $y$ with respect to the law of $Y$, $(X|Y)(y, ·)$ is
    integrable;
 3. the function $u ↦ ∫ (X|Y)(Y(u), v) \, dv$ is integrable;
 4. we have $∫ X(u) \, du = ∫ [∫ (X|Y)(Y(u), v) \, dv] \, du$.

Compared to the revised statement, condition 2 is only claimed almost
everywhere: with no modification on a null set, $κ(y)$ may fail to be
integrable for some $y$. The patched version `condQuantilePatched`, equal to
$0$ at the $y$ where $∫ |x| \, κ(y)(dx) = ∞$ and to $(X|Y)(y, v)$ elsewhere,
satisfies condition 2 for every $y$ (when $X$ is integrable); it agrees with
$X|Y$ for almost every $y$. The key fact is the Galois connection
$(X|Y)(y, v) ≤ x \iff v ≤ F(y, x)$, which follows from the right-continuity
of $F(y, ·)$ and gives both measurability and the law of the sections.
-/

/-- For a finite measure `μ` on `[-∞, ∞]` and `t ≤ μ(univ)`, the generalised inverse
of the CDF satisfies the Galois connection `Q(t) ≤ x ↔ t ≤ μ([-∞, x])`. -/
lemma sInf_le_iff_le_measure_Iic (μ : Measure EReal) [IsFiniteMeasure μ] {t : ENNReal}
    (ht : t ≤ μ Set.univ) (x : EReal) :
    sInf {z | t ≤ μ (Set.Iic z)} ≤ x ↔ t ≤ μ (Set.Iic x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ sInf_le h⟩
  rcases eq_top_or_lt_top x with rfl | hx
  · simpa using ht
  -- `t ≤ μ([-∞, r])` for all `r > x`, then use right-continuity of the CDF
  have key : ∀ r ∈ Set.Ioi x, t ≤ μ (Set.Iic r) := fun r hr ↦ by
    obtain ⟨z, hz, hzr⟩ := sInf_lt_iff.mp (h.trans_lt hr)
    exact hz.trans (measure_mono (Set.Iic_subset_Iic.mpr hzr.le))
  have tend := tendsto_measure_biInter_gt (μ := μ) (s := Set.Iic) (a := x)
    (fun _ _ ↦ measurableSet_Iic.nullMeasurableSet) (fun _ _ _ hij ↦ Set.Iic_subset_Iic.mpr hij)
    ⟨⊤, hx, measure_ne_top _ _⟩
  have hI : ⋂ r > x, Set.Iic r = Set.Iic x := by
    ext z
    simp only [Set.mem_iInter, Set.mem_Iic]
    exact ⟨fun h ↦ le_of_forall_gt_imp_ge_of_dense h, fun h r hr ↦ h.trans hr.le⟩
  rw [hI] at tend
  have : (nhdsWithin x (Set.Ioi x)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, hx⟩
  exact ge_of_tendsto tend (eventually_nhdsWithin_of_forall key)

/-- The conditional quantile function: `(X|Y)(y, v) = inf {x | v ≤ F(y, x)}` where
`F(y, x) = κ(y)([-∞, x])` is the conditional CDF of `X` given `Y = y`. -/
noncomputable def condQuantile (X Y : I → EReal) (p : EReal × I) : EReal :=
  sInf {x | ENNReal.ofReal p.2 ≤ condDistrib X Y volume p.1 (Set.Iic x)}

lemma condQuantile_le_iff (X Y : I → EReal) (y : EReal) (v : I) (x : EReal) :
    condQuantile X Y (y, v) ≤ x ↔ ENNReal.ofReal v ≤ condDistrib X Y volume y (Set.Iic x) :=
  sInf_le_iff_le_measure_Iic _ (by simpa using ENNReal.ofReal_le_one.mpr v.2.2) x

lemma monotone_condQuantile (X Y : I → EReal) (y : EReal) :
    Monotone fun v ↦ condQuantile X Y (y, v) := fun _ _ hvw ↦
  sInf_le_sInf fun _ hx ↦ (ENNReal.ofReal_le_ofReal hvw).trans hx

lemma measurable_condQuantile (X Y : I → EReal) : Measurable (condQuantile X Y) := by
  refine measurable_of_Iic fun x ↦ ?_
  have : condQuantile X Y ⁻¹' Set.Iic x =
      {p | ENNReal.ofReal p.2 ≤ condDistrib X Y volume p.1 (Set.Iic x)} := by
    ext p; exact condQuantile_le_iff X Y p.1 p.2 x
  rw [this]
  exact measurableSet_le
    (ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp measurable_snd))
    (((condDistrib X Y volume).measurable_coe measurableSet_Iic).comp measurable_fst)

/-- Every section of the conditional quantile function has the conditional law. -/
lemma map_condQuantile (X Y : I → EReal) (y : EReal) :
    volume.map (fun v ↦ condQuantile X Y (y, v)) = condDistrib X Y volume y := by
  have hm : Measurable fun v ↦ condQuantile X Y (y, v) :=
    (measurable_condQuantile X Y).comp measurable_prodMk_left
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  set F := condDistrib X Y volume y (Set.Iic x)
  have hF : F ≠ ⊤ := measure_ne_top _ _
  have hF1 : F.toReal ∈ I := ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩
  rw [Measure.map_apply hm measurableSet_Iic]
  have : (fun v ↦ condQuantile X Y (y, v)) ⁻¹' Set.Iic x = Set.Iic ⟨F.toReal, hF1⟩ := by
    ext v
    simp only [Set.mem_preimage, Set.mem_Iic, condQuantile_le_iff, ← Subtype.coe_le_coe]
    exact ENNReal.ofReal_le_iff_le_toReal hF
  rw [this, unitInterval.volume_Iic, ENNReal.ofReal_toReal hF]

/-- **Explicit variant of `exists_cond`.** The conditional quantile function
`(X|Y)(y, v) = inf {x | v ≤ F(y, x)}`, with `F(y, ·)` the conditional CDF of `X`
given `Y = y`, is jointly measurable, nondecreasing in `v`, every section
`(X|Y)(y, ·)` has the conditional law of `X` given `Y = y`, and conditions 1, 3
and 4 hold. Condition 2 only holds for `P_Y`-almost every `y`: the conditional
law can fail to be integrable on a `P_Y`-null set of `y`. -/
theorem condQuantile_spec (X Y : I → EReal) (hX : AEMeasurable X) (hY : AEMeasurable Y) :
    -- 0. joint measurability
    Measurable (condQuantile X Y) ∧
    -- monotonicity in `v`
    (∀ y, Monotone fun v ↦ condQuantile X Y (y, v)) ∧
    -- every section has the conditional law
    (∀ y, volume.map (fun v ↦ condQuantile X Y (y, v)) = condDistrib X Y volume y) ∧
    -- 1. `(u, v) ↦ (Y u, (X|Y) (Y u, v))` under `λ ⊗ λ` has the law of `(Y, X)` under `λ`
    (volume : Measure (I × I)).map (fun p ↦ (Y p.1, condQuantile X Y (Y p.1, p.2))) =
      (volume : Measure I).map (fun u ↦ (Y u, X u)) ∧
    (IntegrableEReal X volume →
      -- 2'. almost every section is integrable
      (∀ᵐ y ∂(volume.map Y), IntegrableEReal (fun v ↦ condQuantile X Y (y, v)) volume) ∧
      -- 3. the inner integral is integrable
      Integrable (fun u ↦ ∫ v, (condQuantile X Y (Y u, v)).toReal) ∧
      -- 4. tower property
      ∫ u, (X u).toReal = ∫ u, ∫ v, (condQuantile X Y (Y u, v)).toReal) := by
  have hQ := measurable_condQuantile X Y
  have hlaw := (map_eq_compProd hY (condDistrib X Y volume) hQ
    (Filter.Eventually.of_forall fun y ↦ map_condQuantile X Y y)).trans
    (compProd_map_condDistrib hY hX)
  refine ⟨hQ, monotone_condQuantile X Y, map_condQuantile X Y, hlaw, fun hXi ↦
    ⟨?_, integrable_and_integral_eq_of_map_eq hX hY hQ hlaw hXi⟩⟩
  filter_upwards [ae_lintegral_condDistrib_lt_top hX hY hXi] with y hy
  have hm : Measurable fun v ↦ condQuantile X Y (y, v) := hQ.comp measurable_prodMk_left
  refine integrableEReal_of_lintegral_lt_top hm ?_
  rwa [← lintegral_map measurable_extNorm hm, map_condQuantile]

/-- The conditional quantile function, set to `0` at the `y` for which the conditional
law `κ(y)` is not integrable (i.e. `∫ |x| dκ(y) = ∞`, with `|±∞| = ∞`). -/
noncomputable def condQuantilePatched (X Y : I → EReal) (p : EReal × I) : EReal :=
  if ∫⁻ x, extNorm x ∂(condDistrib X Y volume p.1) = ⊤ then 0 else condQuantile X Y p

lemma measurable_condQuantilePatched (X Y : I → EReal) :
    Measurable (condQuantilePatched X Y) :=
  Measurable.ite ((measurable_extNorm.lintegral_kernel.comp measurable_fst)
    (measurableSet_singleton ⊤)) measurable_const (measurable_condQuantile X Y)

/-- If `X` is integrable, the patched quantile function agrees with `condQuantile` for
`P_Y`-almost every `y`. -/
lemma ae_condQuantilePatched_eq {X Y : I → EReal} (hX : AEMeasurable X) (hY : AEMeasurable Y)
    (hXi : IntegrableEReal X volume) :
    ∀ᵐ y ∂(volume.map Y), (fun v ↦ condQuantilePatched X Y (y, v)) =
      fun v ↦ condQuantile X Y (y, v) := by
  filter_upwards [ae_lintegral_condDistrib_lt_top hX hY hXi] with y hy
  ext v
  simp [condQuantilePatched, hy.ne]

/-- **Explicit variant of `exists_cond`, with condition 2 for every `y`.** For `X`
integrable, the patched conditional quantile function satisfies all the conditions of
the revised statement: it is jointly measurable, nondecreasing in `v`, its sections
have the conditional law for `P_Y`-almost every `y`, it reproduces the law of `(Y, X)`,
every section is integrable, and the tower property holds. -/
theorem condQuantilePatched_spec (X Y : I → EReal) (hX : AEMeasurable X) (hY : AEMeasurable Y)
    (hXi : IntegrableEReal X volume) :
    -- 0. joint measurability
    Measurable (condQuantilePatched X Y) ∧
    -- monotonicity in `v`
    (∀ y, Monotone fun v ↦ condQuantilePatched X Y (y, v)) ∧
    -- almost every section has the conditional law
    (∀ᵐ y ∂(volume.map Y),
      volume.map (fun v ↦ condQuantilePatched X Y (y, v)) = condDistrib X Y volume y) ∧
    -- 1. `(u, v) ↦ (Y u, (X|Y) (Y u, v))` under `λ ⊗ λ` has the law of `(Y, X)` under `λ`
    (volume : Measure (I × I)).map (fun p ↦ (Y p.1, condQuantilePatched X Y (Y p.1, p.2))) =
      (volume : Measure I).map (fun u ↦ (Y u, X u)) ∧
    -- 2. every section is integrable
    (∀ y, IntegrableEReal (fun v ↦ condQuantilePatched X Y (y, v)) volume) ∧
    -- 3. the inner integral is integrable
    Integrable (fun u ↦ ∫ v, (condQuantilePatched X Y (Y u, v)).toReal) ∧
    -- 4. tower property
    ∫ u, (X u).toReal = ∫ u, ∫ v, (condQuantilePatched X Y (Y u, v)).toReal := by
  have hQ := measurable_condQuantilePatched X Y
  have hsec : ∀ᵐ y ∂(volume.map Y),
      volume.map (fun v ↦ condQuantilePatched X Y (y, v)) = condDistrib X Y volume y := by
    filter_upwards [ae_condQuantilePatched_eq hX hY hXi] with y hy
    rw [hy, map_condQuantile]
  have hlaw := (map_eq_compProd hY (condDistrib X Y volume) hQ hsec).trans
    (compProd_map_condDistrib hY hX)
  refine ⟨hQ, fun y ↦ ?_, hsec, hlaw, fun y ↦ ?_,
    integrable_and_integral_eq_of_map_eq hX hY hQ hlaw hXi⟩
  · by_cases hy : ∫⁻ x, extNorm x ∂(condDistrib X Y volume y) = ⊤
    · simp only [condQuantilePatched, hy, ite_true]
      exact monotone_const
    · simp only [condQuantilePatched, hy, ite_false]
      exact monotone_condQuantile X Y y
  · by_cases hy : ∫⁻ x, extNorm x ∂(condDistrib X Y volume y) = ⊤
    · simp only [condQuantilePatched, hy, ite_true]
      exact ⟨Filter.Eventually.of_forall fun _ ↦ by simp, by simp⟩
    · simp only [condQuantilePatched, hy, ite_false]
      have hm : Measurable fun v ↦ condQuantile X Y (y, v) :=
        (measurable_condQuantile X Y).comp measurable_prodMk_left
      refine integrableEReal_of_lintegral_lt_top hm ?_
      rw [← lintegral_map measurable_extNorm hm, map_condQuantile]
      exact lt_top_iff_ne_top.mpr hy
