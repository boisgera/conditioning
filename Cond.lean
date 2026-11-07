import Mathlib

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
  -- the law of `(Y, X)` is reproduced by any measurable `Ψ` whose sections have law `κ`
  have hlaw : ∀ Ψ : EReal × I → EReal, Measurable Ψ →
      (∀ᵐ y ∂(volume.map Y), volume.map (fun v ↦ Ψ (y, v)) = κ y) →
      (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Ψ (Y p.1, p.2))) =
        (volume : Measure I).map (fun u ↦ (Y u, X u)) := fun Ψ hΨ h ↦
    (map_eq_compProd hY κ hΨ h).trans (compProd_map_condDistrib hY hX)
  have hYfst : AEMeasurable (fun p : I × I ↦ Y p.1) volume := by
    rw [Measure.volume_eq_prod]
    exact hY.comp_quasiMeasurePreserving (measurePreserving_fst.quasiMeasurePreserving)
  have hk : Measurable (fun q : EReal × EReal ↦ q.2.toReal) :=
    measurable_ereal_toReal.comp measurable_snd
  -- Fubini, for any `Ψ` reproducing the law of `(Y, X)`
  have hfub : ∀ Ψ : EReal × I → EReal, Measurable Ψ →
      (volume : Measure (I × I)).map (fun p ↦ (Y p.1, Ψ (Y p.1, p.2))) =
        (volume : Measure I).map (fun u ↦ (Y u, X u)) →
      IntegrableEReal X volume →
      Integrable (fun u ↦ ∫ v, (Ψ (Y u, v)).toReal) ∧
        ∫ u, (X u).toReal = ∫ u, ∫ v, (Ψ (Y u, v)).toReal := by
    intro Ψ hΨ hΨlaw hXi
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
  by_cases hXi : IntegrableEReal X volume
  swap
  · refine ⟨Function.uncurry f, hf, hlaw _ hf (Filter.Eventually.of_forall fun y ↦ hfκ y),
      fun h ↦ absurd h hXi⟩
  -- `F x = |x|`, with the value `∞` at `±∞`
  let F : EReal → ENNReal := fun x ↦ if x = ⊤ ∨ x = ⊥ then ⊤ else ‖x.toReal‖ₑ
  have hF : Measurable F :=
    Measurable.ite ((measurableSet_singleton ⊤).union (measurableSet_singleton ⊥))
      measurable_const measurable_ereal_toReal.enorm
  have hFle : ∀ x, ‖x.toReal‖ₑ ≤ F x := fun x ↦ by
    simp only [F]; split_ifs <;> simp
  let G : EReal → ENNReal := fun y ↦ ∫⁻ x, F x ∂κ y
  have hG : Measurable G := hF.lintegral_kernel
  have hGf : ∀ y, ∫⁻ v, F (f y v) = G y := fun y ↦ by
    simp only [G, ← hfκ y]
    rw [lintegral_map hF (hf.of_uncurry_left)]
  -- `G` is finite almost everywhere for the law of `Y`
  have hGfin : ∀ᵐ y ∂(volume.map Y), G y < ⊤ := by
    refine ae_lt_top hG ?_
    have hYX : AEMeasurable (fun u ↦ (Y u, X u)) volume := hY.prodMk hX
    have : ∫⁻ y, G y ∂(volume.map Y) = ∫⁻ u, F (X u) := by
      have h := Measure.lintegral_compProd (μ := volume.map Y) (κ := κ) (hF.comp measurable_snd)
      simp only [Function.comp_apply] at h
      simp only [G]
      rw [← h, compProd_map_condDistrib hY hX,
        lintegral_map' (f := fun q : EReal × EReal ↦ F q.2)
          (hF.comp measurable_snd).aemeasurable hYX]
    rw [this]
    have hae : ∀ᵐ u ∂(volume : Measure I), F (X u) = ‖(X u).toReal‖ₑ :=
      hXi.1.mono fun u hu ↦ by simp [F, hu.1, hu.2]
    rw [lintegral_congr_ae hae]
    exact (hasFiniteIntegral_iff_enorm.mp hXi.2.2).ne
  let Ψ : EReal × I → EReal := fun p ↦ if G p.1 = ⊤ then 0 else f p.1 p.2
  have hΨ : Measurable Ψ :=
    Measurable.ite ((hG.comp measurable_fst) (measurableSet_singleton ⊤)) measurable_const hf
  have hΨlaw := hlaw Ψ hΨ (hGfin.mono fun y hy ↦ by simp [Ψ, hy.ne, hfκ y])
  refine ⟨Ψ, hΨ, hΨlaw, fun _ ↦ ⟨fun y ↦ ?_, hfub Ψ hΨ hΨlaw hXi⟩⟩
  by_cases hy : G y = ⊤
  · simp only [Ψ, hy]
    exact ⟨Filter.Eventually.of_forall fun _ ↦ by simp, by simp⟩
  · simp only [Ψ, hy, ite_false]
    have hfin : ∫⁻ v, F (f y v) < ⊤ := by rw [hGf]; exact lt_top_iff_ne_top.mpr hy
    have hmeas : Measurable (f y) := hf.of_uncurry_left
    refine ⟨(ae_lt_top (hF.comp hmeas) hfin.ne).mono fun v hv ↦ ?_, ?_⟩
    · by_contra h
      have : F (f y v) = ⊤ := by
        have h' : f y v = ⊤ ∨ f y v = ⊥ := by tauto
        simp only [F, h', ite_true]
      exact hv.ne this
    · exact ⟨(measurable_ereal_toReal.comp hmeas).aestronglyMeasurable,
        hasFiniteIntegral_iff_enorm.mpr ((lintegral_mono fun v ↦ hFle _).trans_lt hfin)⟩
