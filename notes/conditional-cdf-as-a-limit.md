# The conditional CDF as a limit of elementary conditional probabilities

## Setting

Let $(Ω, P) = ([0, 1], λ)$ and let $X, Y : Ω → [-∞, ∞]$ be measurable.
Write $ν = P_Y$ for the law of $Y$ and $κ$ for the conditional law of $X$
given $Y$, i.e. a Markov kernel such that the law of $(Y, X)$ is $ν ⊗ κ$.
Let
$$F(y, x) = κ(y)([-∞, x])$$
be the conditional CDF. Both $κ$ and $F$ are only defined up to a $ν$-null
set of $y$.

To talk about "$Y$ close to $y$" when $y$ may be infinite, equip
$[-∞, ∞]$ with the metric
$$d(s, t) = |φ(s) - φ(t)|, \qquad φ(t) = \frac{t}{1 + |t|}, \quad φ(±∞) = ±1.$$
Then $φ$ is an isometry from $([-∞, ∞], d)$ onto $[-1, 1] ⊂ ℝ$. If $Y$ is
real-valued you can use $|Y - y|$ instead; the proof is the same, working
directly in $ℝ$.

For $ε > 0$, define the *elementary conditional CDF*
$$F_ε(y, x) = \frac{P(X ≤ x,\ d(Y, y) ≤ ε)}{P(d(Y, y) ≤ ε)},$$
the CDF of $X$ given the event $\{d(Y, y) ≤ ε\}$, when that event has
positive probability.

## Theorem

1. **Fixed $x$.** For every $x ∈ [-∞, ∞]$ and $ν$-almost every $y$, we have
   $P(d(Y, y) ≤ ε) > 0$ for all $ε > 0$, and
   $$F_ε(y, x) \xrightarrow[ε → 0^+]{} F(y, x).$$
2. **All $x$ at once.** For $ν$-almost every $y$, this convergence holds
   simultaneously for every $x$ in $D = ℚ ∪ \{-∞, +∞\}$ and every $x$ at
   which $F(y, ·)$ is continuous. Equivalently, for $ν$-almost every $y$,
   $$P(X ∈ · \mid d(Y, y) ≤ ε) \xrightarrow[ε → 0^+]{} κ(y)
   \quad \text{weakly.}$$
3. **Atoms.** If $ν(\{y\}) > 0$, then for every $x$,
   $F_ε(y, x) → P(X ≤ x \mid Y = y)$: at atoms the limit always exists and
   gives the elementary formula.

So, for almost every $y$, $κ(y)$ is given by an explicit formula: take the
limits $\lim_{ε → 0} F_ε(y, q)$ for $q ∈ D$, then extend them to all $x$ by
right-continuity. The catch is "almost every": at a particular $y$ that is
not an atom, the limit may fail to exist. When it does exist, it may still
differ from the value of a given version of $κ$, since versions can be
changed arbitrarily on null sets.

## Proof

**Step 0: the denominators are positive almost everywhere.** Let
$U = \{y \mid ν(\bar B(y, ε)) = 0 \text{ for some } ε > 0\}$, the complement
of the support of $ν$. If $ν(\bar B(y, ε)) = 0$, then
$\bar B(y', ε/2) ⊂ \bar B(y, ε)$ for all $y'$ with $d(y, y') < ε/2$, so $U$
is open, and each point of $U$ has an open neighbourhood of $ν$-measure $0$.
Since $[-∞, ∞]$ is second countable, $U$ is a countable union of such
neighbourhoods, hence $ν(U) = 0$.

**Step 1: $F(·, x)$ is a Radon–Nikodym derivative.** Fix $x$ and define the
measure $μ_x(B) = P(X ≤ x,\ Y ∈ B)$ on $[-∞, ∞]$. By the disintegration
$P_{(Y, X)} = ν ⊗ κ$,
$$μ_x(B) = (ν ⊗ κ)(B × [-∞, x]) = ∫_B κ(y)([-∞, x]) \, ν(dy)
= ∫_B F(y, x) \, ν(dy).$$
So $μ_x ≪ ν$ and $dμ_x / dν = F(·, x)$, $ν$-almost everywhere. Moreover
$$F_ε(y, x) = \frac{μ_x(\bar B(y, ε))}{ν(\bar B(y, ε))}.$$

**Step 2: differentiation of measures.** The *Besicovitch differentiation
theorem* (Mathlib: `Besicovitch.ae_tendsto_rnDeriv`) states that for
locally finite Borel measures $μ, ν$ on $ℝ$ (more generally on $ℝ^n$),
$$\frac{μ(\bar B(y, ε))}{ν(\bar B(y, ε))} \xrightarrow[ε → 0^+]{}
\frac{dμ}{dν}(y) \quad \text{for } ν\text{-almost every } y.$$
No regularity of $ν$ is needed: it may have atoms, or be singular like the
Cantor measure. This is why Besicovitch is needed here rather than the
Lebesgue–Vitali theorem, which requires a doubling condition.

To use it on $[-∞, ∞]$, push $μ_x$ and $ν$ forward by $φ$ to finite measures
on $ℝ$ supported in $[-1, 1]$. Since $φ$ is an isometry onto $[-1, 1]$, we
have $φ(\bar B(y, ε)) = \bar B(φ(y), ε) ∩ [-1, 1]$, so the ratios are
unchanged. Since $φ$ is a Borel isomorphism onto its image, so is the
density: $\frac{d φ_* μ_x}{d φ_* ν} ∘ φ = \frac{dμ_x}{dν}$, $ν$-almost
everywhere. Together with Step 1, this gives $F_ε(y, x) → F(y, x)$ for
$ν$-almost every $y$, which with Step 0 proves part 1.

**Step 3: all $x$ at once.** The set $D$ is countable, so the countable
intersection of the full-measure sets from part 1 still has full measure:
for $ν$-almost every $y$, $F_ε(y, q) → F(y, q)$ for all $q ∈ D$. Fix such a
$y$ and a finite $x$. For $q < x < q'$ in $D$, the map $x ↦ F_ε(y, x)$ is
nondecreasing, so
$$F_ε(y, q) ≤ F_ε(y, x) ≤ F_ε(y, q').$$
Letting $ε → 0$:
$$F(y, q) ≤ \liminf_{ε → 0} F_ε(y, x) ≤ \limsup_{ε → 0} F_ε(y, x) ≤ F(y, q').$$
Letting $q' ↓ x$, right-continuity gives $\limsup ≤ F(y, x)$. Letting
$q ↑ x$ gives $\liminf ≥ F(y, x^-)$. Hence the limit exists and equals
$F(y, x)$ whenever $F(y, ·)$ is continuous at $x$. On the compact space
$[-∞, ∞] ≅ [-1, 1]$, convergence of CDFs at all continuity points of the
limit is equivalent to weak convergence of the laws, which proves part 2.

**Step 4: atoms.** If $ν(\{y\}) > 0$, then $\bar B(y, ε) ↓ \{y\}$ as
$ε ↓ 0$. By continuity of measures from above, the numerator tends to
$P(X ≤ x,\ Y = y)$ and the denominator to $P(Y = y) > 0$. No exceptional set
is involved, which proves part 3. $\blacksquare$

## Remarks

- **Jumps.** At a jump point $x$ of $F(y, ·)$, part 1 still gives
  convergence for $ν$-almost every $y$, but the exceptional set depends on
  $x$. Since there may be uncountably many such pairs $(y, x)$, part 2 only
  claims continuity points. This costs nothing: values on the dense set $D$
  determine $F(y, ·)$ by right-continuity.
- **Centred balls.** The theorem is about balls centred at $y$, which is
  what Besicovitch's covering argument provides.
- **Dimension.** The same statement and proof work for $Y$ with values in
  $ℝ^n$, or in any space with the Besicovitch covering property. It can
  fail in infinite dimension: Preiss (1981) showed that differentiation of
  measures can fail for Gaussian measures on Hilbert space.
- **Relation to Mathlib.** Mathlib's `condDistrib` is not defined by this
  limit. It goes through Radon–Nikodym derivatives at rational $x$
  (`condCDF`). By the theorem, the two agree $ν$-almost everywhere, as any
  two versions of the conditional law must.
