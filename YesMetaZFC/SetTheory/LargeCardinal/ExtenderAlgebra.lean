import YesMetaZFC.SetTheory.LargeCardinal.ExtenderOperator

/-! # 扩展器算子的布尔运算和坐标变换

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
    have hH : M.mem H U := (FilterZF.maximal_decides_d hZF hU (fun s hs => ((hg s).mp hs).1) hh).elim
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
