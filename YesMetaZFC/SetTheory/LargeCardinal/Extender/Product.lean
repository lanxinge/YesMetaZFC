import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber

/-! # 从测度族构造扩展器算子

E(A) 中的支撑恰为其测度集中在 A 上的支撑。输入允许混合有限长度；
整个 E 是定义于全部有限列空间幂集上的实际函数图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_value_d (F S A B : M.Domain) : Prop := ∀ a, M.mem a B ↔ M.mem a S ∧
  ∃ U D, Rd_entry_d a U F ∧ M.mem D U ∧ M.MemberSubset D A

def ex_value_m {d} (F S A B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest S.weaken) (.existsE (.existsE (.conj
    (rd_entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.conj (.mem .newest (.bound 1))
      (Formula.subset .newest A.weaken.weaken.weaken)))))))
derive_free_closed ex_value_m

theorem ex_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (F S A B : Term d) :
    Formula.satisfies ρ (ex_value_m F S A B) ↔ Ex_value_d (F.eval ρ) (S.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [ex_value_m, Ex_value_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    rd_entry_sat_l hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def Ex_operator_d (K S F E : M.Domain) : Prop := ∃ P Q, M.IsPowerSetOf P K ∧ M.IsPowerSetOf Q S ∧
  Fn0_d P Q E ∧ ∀ A B, Rd_entry_d A B E ↔ M.mem A P ∧ Ex_value_d F S A B

theorem ex_operator_exists_l (hZF : M.Models ZF) (K S F : M.Domain) : ∃ E, Ex_operator_d K S F E := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF K
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF S
  let ρ := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push S
  let φ : BinarySchema 2 := { body := ex_value_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat A B : φ.denote ρ A B ↔ Ex_value_d F S A B := ex_value_sat_l hZF.1 _ _ _ _ _
  obtain ⟨E, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := Q)
    (fun A _ => by
      let η := ρ.push A
      let ψ : UnarySchema 3 := { body := .existsE (.existsE (.conj
        (rd_entry_m (.bound 2) (.bound 1) (.bound 5))
        (.conj (.mem .newest (.bound 1)) (Formula.subset .newest (.bound 3))))) }
      obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF ψ η S
      refine ⟨B, (sat A B).mpr fun a => ?_⟩
      simpa only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry_sat_l hZF.1,
        Formula.satisfies_mem_iff, Formula.satisfies_subset_iff] using! hb a)
    (fun A _ B C hb hc => hZF.1.eq_of_same_members B C fun a => ((sat A B).mp hb a).trans ((sat A C).mp hc a).symm)
    (fun A B _ hb => (hQ B).mpr fun a ha => (((sat A B).mp hb a).mp ha).1)
  exact ⟨E, P, Q, hP, hQ, fn0_of_function_l (ZF.modelsKP hZF) he,
    fun A B => (spec A B).trans (and_congr_right fun _ => sat A B)⟩

theorem Ex_operator_d.at_l {K S F E A B : M.Domain} (h : Ex_operator_d K S F E)
    (hab : Rd_entry_d A B E) : M.MemberSubset A K ∧ Ex_value_d F S A B := by
  obtain ⟨_, _, hp, _, _, hs⟩ := h
  exact ⟨(hp A).mp ((hs A B).mp hab).1, ((hs A B).mp hab).2⟩

theorem Ex_operator_d.total_l {K S F E A : M.Domain} (h : Ex_operator_d K S F E)
    (ha : M.MemberSubset A K) : ∃ B, Rd_entry_d A B E := by
  obtain ⟨_, _, hp, _, he, _⟩ := h
  exact (he.2.1 A ((hp A).mpr ha)).imp fun _ hh => hh.2

theorem ex_value_at_l (hE : Extensional M) {ω κ L F S n a U A B : M.Domain}
    (hF : Em_family_d ω κ L F) (haS : M.mem a S) (ha : Fn0_d n L a) (haU : Rd_entry_d a U F)
    (hA : ∀ s, M.mem s A → Fn0_d n κ s) (hv : Ex_value_d F S A B) : M.mem a B ↔ M.mem A U := by
  obtain ⟨m, D, _, hm, hd, hu⟩ := hF.measure a U haU
  have e := hm.domain_eq_l hE ha
  subst m
  exact (hv a).trans ⟨fun ⟨_, V, C, haV, hc, hCA⟩ =>
      hu.1.2.2.1 C A (hF.function a V U haV haU ▸ hc) hCA (fun s hs => (hd s).mpr (hA s hs)),
    fun h => ⟨haS, U, A, haU, h, fun _ => id⟩⟩

theorem ex_value_type_l (hE : Extensional M) {ω κ L F S n A B : M.Domain}
    (hF : Em_family_d ω κ L F) (hA : ∀ s, M.mem s A → Fn0_d n κ s)
    (hv : Ex_value_d F S A B) : ∀ a, M.mem a B → Fn0_d n L a := by
  intro a ha
  obtain ⟨_, U, T, hu, ht, sub⟩ := (hv a).mp ha
  obtain ⟨m, D, _, hm, hd, hU⟩ := hF.measure a U hu
  obtain ⟨s, hs⟩ := hU.2.1 T ht
  have e := ((hd s).mp (hU.1.1 T ht s hs)).domain_eq_l hE (hA s (sub s hs))
  exact e ▸ hm

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩展器算子的布尔运算和坐标变换

这些运算律只读取测度族及协调性；不依赖产生测度的嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Ex_value_d.mono_l {F S A B C D : M.Domain} (h : Ex_value_d F S A B)
    (g : Ex_value_d F S C D) (hc : M.MemberSubset A C) : M.MemberSubset B D := by
  intro a ha
  obtain ⟨hs, U, T, hu, ht, sub⟩ := (h a).mp ha
  exact (g a).mpr ⟨hs, U, T, hu, ht, fun s hs => hc s (sub s hs)⟩

theorem ex_inter_l {ω κ L F S A B C A' B' C' : M.Domain} (hF : Em_family_d ω κ L F)
    (ha : Ex_value_d F S A A') (hb : Ex_value_d F S B B') (hc : Ex_value_d F S C C')
    (hC : ∀ s, M.mem s C ↔ M.mem s A ∧ M.mem s B) :
    ∀ a, M.mem a C' ↔ M.mem a A' ∧ M.mem a B' := by
  intro a
  constructor
  · intro h
    exact ⟨hc.mono_l ha (fun s hs => ((hC s).mp hs).1) a h,
      hc.mono_l hb (fun s hs => ((hC s).mp hs).2) a h⟩
  · rintro ⟨ha', hb'⟩
    obtain ⟨hs, U, D, hu, hd, hdA⟩ := (ha a).mp ha'
    obtain ⟨_, V, E, hv, he, heB⟩ := (hb a).mp hb'
    have e := hF.function a V U hv hu
    subst V
    obtain ⟨_, _, _, _, _, hU⟩ := hF.measure a U hu
    obtain ⟨G, hg, gd, ge⟩ := hU.1.2.2.2 D E hd he
    exact (hc a).mpr ⟨hs, U, G, hu, hg, fun s hs => (hC s).mpr ⟨hdA s (gd s hs), heB s (ge s hs)⟩⟩

theorem ex_compl_l (hZF : M.Models ZF) {ω κ L F K S A B A' B' : M.Domain}
    (hF : Em_family_d ω κ L F) (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (ha : Ex_value_d F S A A') (hb : Ex_value_d F S B B')
    (hB : ∀ s, M.mem s B ↔ M.mem s K ∧ ¬ M.mem s A) :
    ∀ a, M.mem a B' ↔ M.mem a S ∧ ¬ M.mem a A' := by
  intro a
  constructor
  · intro hx
    obtain ⟨hs, U, D, hu, hd, hdB⟩ := (hb a).mp hx
    refine ⟨hs, fun hy => ?_⟩
    obtain ⟨_, V, E, hv, he, heA⟩ := (ha a).mp hy
    have e := hF.function a V U hv hu
    subst V
    obtain ⟨_, _, _, _, _, hU⟩ := hF.measure a U hu
    obtain ⟨G, hg, gd, ge⟩ := hU.1.2.2.2 D E hd he
    obtain ⟨s, hs⟩ := hU.2.1 G hg
    exact ((hB s).mp (hdB s (gd s hs))).2 (heA s (ge s hs))
  · rintro ⟨hs, hn⟩
    obtain ⟨n, hnω, hna⟩ := (hS a).mp hs
    obtain ⟨U, hu⟩ := hF.total n a hnω (fn0_of_function_l (ZF.modelsKP hZF) hna)
    obtain ⟨m, D, hm, _, hD, hU⟩ := hF.measure a U hu
    obtain ⟨G, hg⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) D A
    obtain ⟨H, hh⟩ := KP.difference_exists_d (ZF.modelsKP hZF) G D
    obtain ⟨P, power⟩ := ZF.exists_powerSet hZF D
    have hH : M.mem H U := (FilterZF.maximal_decides_d (ZF.modelsKP hZF) power hU (fun s hs => ((hg s).mp hs).1) hh).elim
      (fun hx => (hn ((ha a).mpr ⟨hs, U, G, hu, hx, fun s ht => ((hg s).mp ht).2⟩)).elim) id
    refine (hb a).mpr ⟨hs, U, H, hu, hH, fun s ht => ?_⟩
    obtain ⟨hsD, hsG⟩ := (hh s).mp ht
    exact (hB s).mpr ⟨(hK s).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hsD)⟩,
      fun hsA => hsG ((hg s).mpr ⟨hsD, hsA⟩)⟩

/-- 任意有限坐标函数的逆像与扩展器交换，含置换、遗漏和重复坐标。 -/
theorem ex_reindex_l (hZF : M.Models ZF) {ω κ L F S m n q a b U V A B A' B' : M.Domain}
    (hF : Em_family_d ω κ L F) (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hm : M.mem m ω) (hn : M.mem n ω) (hq : Fn0_d m n q) (ha : Fn0_d n L a)
    (hab : Cp0_d m n L q a b) (haS : M.mem a S) (hbS : M.mem b S)
    (haV : Rd_entry_d a V F) (hbU : Rd_entry_d b U F) (hA : ∀ s, M.mem s A → Fn0_d m κ s)
    (hB : Es_pull_d m n κ q A B) (heA : Ex_value_d F S A A') (heB : Ex_value_d F S B B') :
    M.mem a B' ↔ M.mem b A' := by
  obtain ⟨Z, hz, hu⟩ := hc m n q a b U V A hm hn hq ha hab haV hbU hA
  have e := hZF.1.eq_of_same_members Z B fun s => (hz s).trans (hB s).symm
  subst Z
  exact (ex_value_at_l hZF.1 hF haS ha haV (fun s hs => ((hB s).mp hs).1) heB).trans
    (hu.trans (ex_value_at_l hZF.1 hF hbS hab.1 hbU hA heA).symm)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩展器保持有限坐标上的乘积

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
