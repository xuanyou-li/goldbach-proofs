import Mathlib

open Finset

/-- The inverse volume bounds the total contribution from a sparse exceptional set.
The rectangle error is small on every target outside that set. -/
theorem Conjectures.Cuts.Cut1e6df45eff86addf24fae2f8
    -- child 1 zh: 立方根筛点的归一化体积有一致的 n 除以对数平方下界
    -- child 1 en: Uniform logarithmic lower bound for the sieve volume at the cube-root cutoff
    (hVolume :
      let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
      let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime
      let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n *
        ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
      let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ n ≥ T, Even n →
        (n : ℝ)+1 ≤ C*(Real.log ((n : ℝ)+2))^2*V n (Z₁ n))
    -- child 2 zh: 半素数因子矩形的归一化误差超过固定正阈值的偶数只有对数四次节省的比例
    -- child 2 en: Fourth-power logarithmic saving on the exceptional targets for the normalized rectangle count
    (hException :
      let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
      let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime
      let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n *
        ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
      let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      let B := fun X : ℕ => (Finset.Icc X (2*X)).filter Even
      let box := fun (n u : ℕ) (a b : ℝ) =>
        u.primeFactorsList.length=2 ∧ (n:ℝ)^a < (u.minFac:ℝ) ∧ (u.minFac:ℝ) ≤ (n:ℝ)^b
      let w := fun a b : ℝ => Real.log ((b*(1-a))/(a*(1-b)))
      ∀ a b c d : ℝ, 1/3 ≤ a → a < b → b ≤ 1/2 → 1/3 ≤ c → c < d → d ≤ 1/2 →
        ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ X ≥ T,
        let R := fun n : ℕ => ((I n).filter (fun u =>
          u.Coprime n ∧ box n u a b ∧ box n (n-u) c d)).card
        let K := (Real.exp Real.eulerMascheroniConstant/3)^2*w a b*w c d
        (((B X).filter (fun n => ε < |(R n:ℝ)/V n (Z₁ n)-K|)).card : ℝ) ≤
          ((B X).card : ℝ) / (Real.log ((X : ℝ)+2))^4) : (by
  classical
  exact let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let S := fun n z : ℕ => ((I n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card; let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B := fun X : ℕ => (Finset.Icc X (2*X)).filter Even; let box := fun (n u : ℕ) (a b : ℝ) => u.primeFactorsList.length=2 ∧ (n:ℝ)^a < (u.minFac:ℝ) ∧ (u.minFac:ℝ) ≤ (n:ℝ)^b; let w := fun a b : ℝ => Real.log ((b*(1-a))/(a*(1-b))); ∀ a b c d : ℝ, 1/3 ≤ a → a < b → b ≤ 1/2 → 1/3 ≤ c → c < d → d ≤ 1/2 → ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ X ≥ T, let R := fun n : ℕ => ((I n).filter (fun u => u.Coprime n ∧ box n u a b ∧ box n (n-u) c d)).card; let K := (Real.exp Real.eulerMascheroniConstant/3)^2*w a b*w c d; (∑ n ∈ B X, |(R n:ℝ)/V n (Z₁ n)-K|) ≤ ε*((B X).card:ℝ)) := by
  classical
  have sum_abs_le_of_exceptional_count (box : Finset ℕ) (error : ℕ → ℝ)
      {ε bound count : ℝ} (hε : 0 ≤ ε) (hbound : 0 ≤ bound)
      (hpoint : ∀ n ∈ box, |error n| ≤ bound)
      (hcount : ((box.filter fun n => ε < |error n|).card : ℝ) ≤ count) :
      ∑ n ∈ box, |error n| ≤ ε * (box.card : ℝ) + bound * count := by
    classical
    let bad := box.filter fun n => ε < |error n|
    let good := box.filter fun n => ¬ ε < |error n|
    have hbad : ∑ n ∈ bad, |error n| ≤ bound * (bad.card : ℝ) := by
      calc
        _ ≤ ∑ _ ∈ bad, bound := sum_le_sum fun n hn => hpoint n (mem_filter.mp hn).1
        _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
    have hgood : ∑ n ∈ good, |error n| ≤ ε * (good.card : ℝ) := by
      calc
        _ ≤ ∑ _ ∈ good, ε := sum_le_sum fun _ hn => not_lt.mp (mem_filter.mp hn).2
        _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
    have hsize : (good.card : ℝ) ≤ box.card := by
      exact_mod_cast card_filter_le box (fun n => ¬ ε < |error n|)
    have hsplit : (∑ n ∈ bad, |error n|) + (∑ n ∈ good, |error n|) =
        ∑ n ∈ box, |error n| :=
      sum_filter_add_sum_filter_not box (fun n => ε < |error n|) (fun n => |error n|)
    rw [← hsplit]
    exact (add_le_add (hbad.trans (mul_le_mul_of_nonneg_left hcount hbound))
      (hgood.trans (mul_le_mul_of_nonneg_left hsize hε))).trans_eq (add_comm _ _)

  have mean_abs_le_of_log_sparse_exceptions (B : ℕ → Finset ℕ) (error : ℕ → ℝ)
      (hbound : ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ X ≥ T, ∀ n ∈ B X,
        |error n| ≤ C * (Real.log ((X : ℝ) + 2))^2)
      (hrare : ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ X ≥ T,
        (((B X).filter fun n => ε < |error n|).card : ℝ) ≤
          ((B X).card : ℝ) / (Real.log ((X : ℝ) + 2))^4) :
      ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ X ≥ T,
        ∑ n ∈ B X, |error n| ≤ ε * ((B X).card : ℝ) := by
    obtain ⟨C, hC, Tbound, hpoint⟩ := hbound
    intro ε hε
    obtain ⟨Trare, hcount⟩ := hrare (ε/2) (by positivity)
    obtain ⟨Tlog, hlogStart⟩ := exists_nat_ge (Real.exp (1+2*C/ε))
    refine ⟨max Tlog (max Tbound Trare), ?_⟩
    intro X hX
    have hTbound := (le_max_left Tbound Trare).trans ((le_max_right Tlog _).trans hX)
    have hTrare := (le_max_right Tbound Trare).trans ((le_max_right Tlog _).trans hX)
    have hTlog := (le_max_left Tlog _).trans hX
    let L := Real.log ((X : ℝ) + 2)
    have hL : 1+2*C/ε ≤ L := by
      rw [← Real.log_exp (1+2*C/ε)]
      apply Real.log_le_log (Real.exp_pos _)
      exact hlogStart.trans (by
        have hcast : (Tlog : ℝ) ≤ X := by exact_mod_cast hTlog
        linarith)
    have hLone : 1 ≤ L := by linarith [div_nonneg (by positivity : 0 ≤ 2*C) hε.le]
    have hLpos : 0 < L := by linarith
    have hCsmall : C / L^2 ≤ ε/2 := by
      apply (div_le_iff₀ (pow_pos hLpos 2)).2
      have hmul := mul_le_mul_of_nonneg_left
        (show 2*C/ε ≤ L by linarith) (by positivity : 0 ≤ ε/2)
      have heq : (ε/2)*(2*C/ε) = C := by field_simp
      have hsq : L ≤ L^2 := by nlinarith [mul_nonneg hLpos.le (sub_nonneg.mpr hLone)]
      exact (heq ▸ hmul).trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    have havg := sum_abs_le_of_exceptional_count (B X) error
      (by positivity : 0 ≤ ε/2) (by positivity : 0 ≤ C*L^2)
      (hpoint X hTbound) (hcount X hTrare)
    calc
      _ ≤ (ε/2)*((B X).card : ℝ) + (C*L^2)*((B X).card / L^4) := havg
      _ = (ε/2)*((B X).card : ℝ) + (C/L^2)*((B X).card : ℝ) := by
        field_simp
      _ ≤ (ε/2)*((B X).card : ℝ) + (ε/2)*((B X).card : ℝ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hCsmall (Nat.cast_nonneg (B X).card))
      _ = _ := by ring
  dsimp only
  intro a b c d ha hab hb hc hcd hd
  let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
  let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime
  let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n *
    ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
  let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  let B := fun X : ℕ => (Finset.Icc X (2*X)).filter Even
  let box := fun (n u : ℕ) (a b : ℝ) =>
    u.primeFactorsList.length=2 ∧ (n:ℝ)^a < (u.minFac:ℝ) ∧ (u.minFac:ℝ) ≤ (n:ℝ)^b
  let R := fun n : ℕ => ((I n).filter (fun u =>
    u.Coprime n ∧ box n u a b ∧ box n (n-u) c d)).card
  let w := fun a b : ℝ => Real.log ((b*(1-a))/(a*(1-b)))
  let K := (Real.exp Real.eulerMascheroniConstant/3)^2*w a b*w c d
  let error := fun n : ℕ => (R n:ℝ)/V n (Z₁ n)-K
  change ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ X ≥ T,
    ∑ n ∈ B X, |error n| ≤ ε*((B X).card : ℝ)
  refine mean_abs_le_of_log_sparse_exceptions B error ?_
    (hException a b c d ha hab hb hc hcd hd)
  · obtain ⟨C, hC, T, hvol⟩ := hVolume
    obtain ⟨Tlog, hTlog⟩ := exists_nat_ge (Real.exp 1)
    refine ⟨4*C+|K|+1, by positivity, max T Tlog, ?_⟩
    intro X hX n hn
    obtain ⟨hnBounds, hnEven⟩ := mem_filter.mp hn
    obtain ⟨hnLower, hnUpper⟩ := mem_Icc.mp hnBounds
    have hnT := ((le_max_left T Tlog).trans hX).trans hnLower
    have hv : (n : ℝ)+1 ≤ C*(Real.log ((n : ℝ)+2))^2*V n (Z₁ n) :=
      hvol n hnT hnEven
    have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hXNonneg : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hlogn : 0 < Real.log ((n : ℝ)+2) := Real.log_pos (by linarith)
    have hvolume : 0 < V n (Z₁ n) := by
      by_contra! hnVolume
      have hle := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ C*(Real.log ((n : ℝ)+2))^2 by positivity) hnVolume
      linarith
    have hRcard : (R n : ℝ) ≤ (n : ℝ)+1 := by
      have hfilter : R n ≤ (I n).card :=
        card_filter_le (I n) (fun u => u.Coprime n ∧ box n u a b ∧ box n (n-u) c d)
      have hsubset : I n ⊆ Finset.range (n+1) := by
        intro u hu
        have hu_upper : u ≤ 2*n/3 := (mem_Icc.mp hu).2
        exact mem_range.mpr (by omega)
      have htotal : R n ≤ n+1 := hfilter.trans (by
        simpa only [card_range] using card_le_card hsubset)
      exact_mod_cast htotal
    have hquot : (R n : ℝ)/V n (Z₁ n) ≤ C*(Real.log ((n : ℝ)+2))^2 :=
      (div_le_iff₀ hvolume).2 (hRcard.trans hv)
    have hnRealUpper : (n : ℝ) ≤ 2*(X : ℝ) := by exact_mod_cast hnUpper
    have hlogX : 1 ≤ Real.log ((X : ℝ)+2) := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos _)
      have hcast : (Tlog : ℝ) ≤ X := by
        exact_mod_cast (le_max_right T Tlog).trans hX
      linarith [hTlog.trans hcast]
    have hlogCmp : Real.log ((n : ℝ)+2) ≤ 2*Real.log ((X : ℝ)+2) := by
      calc
        _ ≤ Real.log (((X : ℝ)+2)^2) := by
          apply Real.log_le_log (by positivity)
          nlinarith [sq_nonneg (X : ℝ)]
        _ = _ := by norm_num [Real.log_pow]
    have hsq := pow_le_pow_left₀ hlogn.le hlogCmp 2
    have hlogXSq : 1 ≤ (Real.log ((X : ℝ)+2))^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlogX) (show
        0 ≤ Real.log ((X : ℝ)+2) by linarith)]
    have hquotNonneg : 0 ≤ (R n : ℝ)/V n (Z₁ n) :=
      div_nonneg (Nat.cast_nonneg (R n)) hvolume.le
    calc
      |error n| ≤ (R n : ℝ)/V n (Z₁ n)+|K| := by
        simpa only [error, sub_eq_add_neg, abs_neg, abs_of_nonneg hquotNonneg]
          using abs_add_le ((R n : ℝ)/V n (Z₁ n)) (-K)
      _ ≤ 4*C*(Real.log ((X : ℝ)+2))^2+|K| := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
      _ ≤ (4*C+|K|+1)*(Real.log ((X : ℝ)+2))^2 := by
        nlinarith [mul_le_mul_of_nonneg_left hlogXSq (abs_nonneg K)]
