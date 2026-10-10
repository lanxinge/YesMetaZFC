import YesMetaZFC.SetTheory.LargeCardinal.ExtenderAlgebra

/-! # 扩展器保持有限坐标上的乘积

用两张实际坐标图描述乘积；普通分块乘积、共享坐标的纤维积及对角限制
均由同一方程处理。源乘积由分离构造，保持律只消费协调性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_product_d (κ m n l q r A B C : M.Domain) : Prop := ∀ s, M.mem s C ↔ Fn0_d l κ s ∧
  ∃ a b, M.mem a A ∧ M.mem b B ∧ Cp0_d m l κ q s a ∧ Cp0_d n l κ r s b

def ex_product_at_m {d} (κ m n l q r A B s : Term d) : Formula 1 d :=
  Formula.existsMem A (Formula.existsMem B.weaken (.conj
    (cp0_m m.weaken.weaken l.weaken.weaken κ.weaken.weaken q.weaken.weaken s.weaken.weaken (.bound 1))
    (cp0_m n.weaken.weaken l.weaken.weaken κ.weaken.weaken r.weaken.weaken s.weaken.weaken .newest)))
derive_free_closed ex_product_at_m
theorem ex_product_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ m n l q r A B s : Term d) :
    Formula.satisfies ρ (ex_product_at_m κ m n l q r A B s) ↔ ∃ a b, M.mem a (A.eval ρ) ∧ M.mem b (B.eval ρ) ∧
      Cp0_d (m.eval ρ) (l.eval ρ) (κ.eval ρ) (q.eval ρ) (s.eval ρ) a ∧
      Cp0_d (n.eval ρ) (l.eval ρ) (κ.eval ρ) (r.eval ρ) (s.eval ρ) b := by
  simp only [ex_product_at_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    cp0_sat_l hE, Definitional.Term.eval_weaken]
  exact exists_congr fun a => ⟨fun ⟨ha, b, hb, hq, hr⟩ => ⟨b, ha, hb, hq, hr⟩,
    fun ⟨b, ha, hb, hq, hr⟩ => ⟨ha, b, hb, hq, hr⟩⟩

theorem ex_product_exists_l (hZF : M.Models ZF) (κ m n l q r A B : M.Domain) :
    ∃ C, Ex_product_d κ m n l q r A B C := by
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) l κ
  let ρ := (((((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push m).push n).push l).push q).push r).push A).push B
  let φ : UnarySchema 8 := {
    body := ex_product_at_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF φ ρ D
  exact ⟨C, fun s => (hc s).trans (and_congr ((hD s).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)
    (ex_product_at_sat_l hZF.1 _ _ _ _ _ _ _ _ _ _))⟩

theorem ex_product_l (hZF : M.Models ZF) {ω κ L F S m n l q r A B C A' B' C' : M.Domain}
    (hF : Em_family_d ω κ L F) (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hm : M.mem m ω) (hn : M.mem n ω) (hl : M.mem l ω) (hq : Fn0_d m l q) (hr : Fn0_d n l r)
    (hA : ∀ s, M.mem s A → Fn0_d m κ s) (hB : ∀ s, M.mem s B → Fn0_d n κ s)
    (hC : Ex_product_d κ m n l q r A B C)
    (heA : Ex_value_d F S A A') (heB : Ex_value_d F S B B') (heC : Ex_value_d F S C C') :
    Ex_product_d L m n l q r A' B' C' := by
  have typeC s (hs : M.mem s C) := ((hC s).mp hs).1
  have point c (hf : Fn0_d l L c) a b (hqa : Cp0_d m l L q c a) (hrb : Cp0_d n l L r c b) :
      M.mem c C' ↔ M.mem a A' ∧ M.mem b B' := by
    obtain ⟨U, haU⟩ := hF.total m a hm hqa.1
    obtain ⟨V, hbV⟩ := hF.total n b hn hrb.1
    obtain ⟨W, hcW⟩ := hF.total l c hl hf
    obtain ⟨P, hp, hPU⟩ := hc m l q c a U W A hm hl hq hf hqa hcW haU hA
    obtain ⟨Q, hq', hQV⟩ := hc n l r c b V W B hn hl hr hf hrb hcW hbV hB
    have inter s : M.mem s C ↔ M.mem s P ∧ M.mem s Q := by
      refine (hC s).trans ⟨?_, ?_⟩
      · rintro ⟨hs, a, b, ha, hb, hqa, hrb⟩
        exact ⟨(hp s).mpr ⟨hs, a, ha, hqa⟩, (hq' s).mpr ⟨hs, b, hb, hrb⟩⟩
      · rintro ⟨hP, hQ⟩
        obtain ⟨hs, a, ha, hqa⟩ := (hp s).mp hP
        obtain ⟨_, b, hb, hrb⟩ := (hq' s).mp hQ
        exact ⟨hs, a, b, ha, hb, hqa, hrb⟩
    obtain ⟨d, D, _, hd, hD, hW⟩ := hF.measure c W hcW
    have ed := hd.domain_eq_l hZF.1 hf
    subst d
    have meet : M.mem C W ↔ M.mem P W ∧ M.mem Q W := by
      refine ⟨fun hC => ⟨?_, ?_⟩, fun h => FilterZF.inter_mem_d hW.1 h.1 h.2 inter⟩
      · exact hW.1.2.2.1 C P hC (fun s hs => ((inter s).mp hs).1) (fun s hs => (hD s).mpr (((hp s).mp hs).1))
      · exact hW.1.2.2.1 C Q hC (fun s hs => ((inter s).mp hs).2) (fun s hs => (hD s).mpr (((hq' s).mp hs).1))
    have seed t v (ht : M.mem t ω) (hv : Fn0_d t L v) := (hS v).mpr ⟨t, ht, fn0_function_l (ZF.modelsKP hZF) hv⟩
    exact (ex_value_at_l hZF.1 hF (seed l c hl hf) hf hcW typeC heC).trans (meet.trans
      (and_congr (hPU.trans (ex_value_at_l hZF.1 hF (seed m a hm hqa.1) hqa.1 haU hA heA).symm)
        (hQV.trans (ex_value_at_l hZF.1 hF (seed n b hn hrb.1) hrb.1 hbV hB heB).symm)))
  intro c
  constructor
  · intro hc
    have hf := ex_value_type_l hZF.1 hF typeC heC c hc
    obtain ⟨a, ha⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hf
    obtain ⟨b, hb⟩ := cp0_exists_l (ZF.modelsKP hZF) hr hf
    obtain ⟨haA, hbB⟩ := (point c hf a b ha hb).mp hc
    exact ⟨hf, a, b, haA, hbB, ha, hb⟩
  · rintro ⟨hf, a, b, haA, hbB, ha, hb⟩
    exact (point c hf a b ha hb).mpr ⟨haA, hbB⟩

end YesMetaZFC.SetTheory.LargeCardinal
