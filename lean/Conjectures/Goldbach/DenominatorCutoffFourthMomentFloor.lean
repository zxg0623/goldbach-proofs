import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-!
The first block of squarefree denominators above a cutoff forces a fourth
moment on its exterior. The constant and the threshold are uniform in the
cutoff and in the arc width. We use the reduced-residue amplitude estimate and
the disjoint-window integration from the square-root exterior second moment.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators Interval Topology
open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open Conjectures.Goldbach.SqrtArcSecondMomentFloor.GoldbachSupport

namespace Conjectures.Goldbach.DenominatorCutoffFourthMomentFloor

/-- At denominators at most eight times the cutoff, the second moment across
the reduced numerators itself satisfies an amplitude lower bound after scaling. -/
private theorem rescaledAmplitude {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    {n D : ℝ} {q : ℕ} (hn : 0 < n) (hD : 0 ≤ D) (hq : 0 < q)
    (hsize : (q : ℝ) ≤ 8 * D) (hcard : s.card ≤ q)
    (hamp : n / 8 ≤ ‖∑ a ∈ s, z a‖) :
    n / 8 ≤ ‖∑ a ∈ s, ((64 * D / n * ‖z a‖ ^ 2 : ℝ) : ℂ)‖ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have he := residueEnergy s z hn.le hq hcard hamp
  have he' := (div_le_iff₀ (show (0 : ℝ) < 64 * q by positivity)).mp he
  have hs : 0 ≤ ∑ a ∈ s, ‖z a‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  rw [← Complex.ofReal_sum, ← Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) hs), div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).2
  nlinarith only [he', mul_le_mul_of_nonneg_right hsize hs]

private theorem integral_rescale (A : Set ℝ) (S : ℝ → ℂ) (b : ℝ) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..1, A.indicator (fun u => ‖((b * ‖S u‖ ^ 2 : ℝ) : ℂ)‖ ^ 2) t) =
      b ^ 2 * ∫ t in (0 : ℝ)..1, A.indicator (fun u => ‖S u‖ ^ 4) t := by
  classical
  have point (t : ℝ) : A.indicator (fun u => ‖((b * ‖S u‖ ^ 2 : ℝ) : ℂ)‖ ^ 2) t =
      b ^ 2 * A.indicator (fun u => ‖S u‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hb (sq_nonneg _))]
      ring
    · simp [Set.indicator_of_notMem ht]
  simp_rw [point]
  rw [intervalIntegral.integral_const_mul]

private theorem fourthFloor :
    ∀ᶠ n : ℕ in atTop, ∀ D H : ℕ, 0 < D → 32 * (D : ℝ) ≤ Real.sqrt n →
      (H : ℝ) ≤ Real.sqrt n →
      (n : ℝ) ^ 3 ≤ 12582912 * (D : ℝ) ^ 2 *
        ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator
          (fun u => ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 4) t := by
  classical
  filter_upwards [primeAmplitudeBounds] with n hprime
  obtain ⟨hn, hθ, hlog⟩ := hprime
  intro D H hd hcut hH
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hfit : 8 * D ≤ ⌊Real.sqrt n / 4⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith only [hcut]
  obtain ⟨hend, hmask, hpair⟩ :=
    denominatorWindowLimits n D H hn (by linarith only [hcut, hD]) hH
  let s := (Finset.Ioc D (8 * D)).filter Squarefree
  have hs {q : ℕ} (hq : q ∈ s) : (D < q ∧ q ≤ 8 * D) ∧ Squarefree q := by
    simpa [s] using hq
  have hmass : (1 / 8 : ℝ) * 1 ≤ ∑ q ∈ s, 1 / (q : ℝ) := by
    simpa [s, GoldbachCount.mass] using GoldbachCount.mass_blocks D 1 hd
  let b : ℝ := 64 * D / n
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  let T := fun t : ℝ => ((b * ‖GoldbachL2Arithmetic.primeSum n t‖ ^ 2 : ℝ) : ℂ)
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hw := assembleWindows s D H n T hT hn0
    (fun _ hq => (hs hq).1.1)
    (fun q hq => hend q ((hs hq).1.2.trans hfit))
    (fun q hq => hmask q ((hs hq).1.2.trans hfit))
    (fun q hq r hr => hpair q r ((hs hq).1.2.trans hfit) ((hs hr).1.2.trans hfit))
    (by
      intro q hq h hh
      apply rescaledAmplitude _ (fun a : ℕ => GoldbachL2Arithmetic.primeSum n ((a : ℝ) / q + h))
        hnR hD (hd.trans (hs hq).1.1)
      · exact_mod_cast (hs hq).1.2
      · exact (Finset.card_filter_le ..).trans_eq (Finset.card_range q)
      · exact GoldbachL2Arithmetic.reduced_amplitude n q hn0 (hs hq).2 hθ
          (hlog q ((hs hq).1.2.trans hfit)) h hh.1 hh.2)
  let I := ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator
    (fun u => ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 4) t
  have hscaled : (n : ℝ) / 3072 ≤ b ^ 2 * I := by
    have h := (scaleDenominatorMass s n (1 / 8) 1 hmass).trans hw
    change _ ≤ ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator
      (fun u => ‖((b * ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 2 : ℝ) : ℂ)‖ ^ 2) t at h
    rw [integral_rescale _ _ b hb] at h
    change _ ≤ b ^ 2 * I at h
    linarith only [h]
  have hbn : b ^ 2 * (n : ℝ) ^ 2 = 4096 * (D : ℝ) ^ 2 := by
    dsimp [b]
    field_simp
    ring
  change _ ≤ 12582912 * (D : ℝ) ^ 2 * I
  calc
    (n : ℝ) ^ 3 = 3072 * ((n : ℝ) / 3072 * (n : ℝ) ^ 2) := by ring
    _ ≤ 3072 * ((b ^ 2 * I) * (n : ℝ) ^ 2) := by gcongr
    _ = 3072 * ((b ^ 2 * (n : ℝ) ^ 2) * I) := by ring
    _ = 12582912 * (D : ℝ) ^ 2 * I := by rw [hbn]; ring

end Conjectures.Goldbach.DenominatorCutoffFourthMomentFloor

open Conjectures.Goldbach.DenominatorCutoffFourthMomentFloor in
/-- Uniform fourth-moment lower bound beyond a variable denominator cutoff. -/
theorem Conjectures.Goldbach.DenominatorCutoffFourthMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)
    let arcs := fun (n D H : ℕ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)}
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D H : ℕ, 0 < D → 32 * (D : ℝ) ≤ Real.sqrt n →
      (H : ℝ) ≤ Real.sqrt n →
      (n : ℝ) ^ 3 ≤ 12582912 * (D : ℝ) ^ 2 *
        intervalIntegral (fun t => (arcs n D H)ᶜ.indicator (fun u => ‖S n u‖ ^ 4) t)
          (0 : ℝ) 1 MeasureTheory.volume := by
  simpa only [GoldbachL2Arithmetic.primeSum_eq_catalogue, GoldbachL2Arithmetic.E,
    publishedWideArcs] using Filter.eventually_atTop.1 fourthFloor
