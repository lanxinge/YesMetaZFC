import YesMetaZFC.SetTheory.LargeCardinal.SupportIndex
import YesMetaZFC.SetTheory.LargeCardinal.Coherence
import YesMetaZFC.SetTheory.Filter.Finite

/-! # 有限支撑测度的共同约束

约束沿唯一坐标映射拉回；无包含关系时约束为空。有限多个约束的共同细化
仍为测度一，不借用各分量的可数完备性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

structure Em_family_d (ω κ L F : M.Domain) : Prop where
  total : ∀ n a, M.mem n ω → Fn0_d n L a → ∃ U, Rd_entry_d a U F
  function : ∀ a U V, Rd_entry_d a U F → Rd_entry_d a V F → U = V
  measure : ∀ a U, Rd_entry_d a U F → ∃ n D, M.mem n ω ∧ Fn0_d n L a ∧
    (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧ Maximal_d (ℳ := M) D U

theorem Em_family_d.at_l (hE : Extensional M) {ω κ L F a U n D : M.Domain}
    (h : Em_family_d ω κ L F) (ha : Rd_entry_d a U F) (hn : Fn0_d n L a)
    (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s) : Maximal_d (ℳ := M) D U := by
  obtain ⟨m, E, _, hm, he, hu⟩ := h.measure a U ha
  have en := hm.domain_eq_l hE hn
  subst m
  exact hE.eq_of_same_members E D (fun s => (he s).trans (hD s).symm) ▸ hu

/-- 已构造的派生测度族给出不提原嵌入的测度族接口。 -/
theorem es_measures_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F) : Em_family_d ω κ L F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun n a hn ha => (hF.2.1 a).mp ((hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩),
    hF.1.2, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hD, _, hu, _⟩ := es_family_ultra_l I hZF hω hX hδ h hY hc hL hS hSY hF ha
  obtain ⟨m, hm, hma⟩ := (hS a).mp ((hF.2.2 a U).mp ha).1
  have e := (fn0_of_function_l (ZF.modelsKP hZF) hma).domain_eq_l hZF.1 hn
  exact ⟨n, D, e ▸ hm, hn, hD, hu⟩

def Ec_ok_d (κ L a c E s : M.Domain) : Prop := ∀ m n q, Fn0_d m n q → Fn0_d n L c →
  Cp0_d m n L q c a → ∃ r, M.mem r E ∧ Cp0_d m n κ q s r

def ec_ok_m {d} (κ L a c E s : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (fn0_m (.bound 2) (.bound 1) .newest) (.imp (fn0_m (.bound 1) L.weaken.weaken.weaken c.weaken.weaken.weaken)
    (.imp (cp0_m (.bound 2) (.bound 1) L.weaken.weaken.weaken .newest c.weaken.weaken.weaken a.weaken.weaken.weaken)
      (Formula.existsMem E.weaken.weaken.weaken (cp0_m (.bound 3) (.bound 2) κ.weaken.weaken.weaken.weaken
        (.bound 1) s.weaken.weaken.weaken.weaken .newest)))))))
derive_free_closed ec_ok_m

theorem ec_ok_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L a c E s : Term d) :
    Formula.satisfies ρ (ec_ok_m κ L a c E s) ↔
      Ec_ok_d (κ.eval ρ) (L.eval ρ) (a.eval ρ) (c.eval ρ) (E.eval ρ) (s.eval ρ) := by
  simp only [ec_ok_m, Ec_ok_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, cp0_sat_l hE, Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]; rfl

theorem ec_ok_iff_l (hE : Extensional M) {κ L m n a c E s q : M.Domain}
    (hc : Fn0_d n L c) (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hq : Fn0_d m n q) (ha : Cp0_d m n L q c a) :
    Ec_ok_d κ L a c E s ↔ ∃ r, M.mem r E ∧ Cp0_d m n κ q s r := by
  refine ⟨fun h => h m n q hq hc ha, fun h m' n' q' hq' hc' ha' => ?_⟩
  have e := hc'.domain_eq_l hE hc
  subst n'
  have e := ha'.1.domain_eq_l hE ha.1
  subst m'
  exact ec_factor_unique_l hE hinj hq hq' ha ha' ▸ h

/-- 一个有限支撑约束在任意包含它的单射支撑上仍为测度一。 -/
theorem ec_test_l (hZF : M.Models ZF) {ω κ L F m n a c U V E D : M.Domain}
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hm : M.mem m ω) (hn : M.mem n ω) (ha : Fn0_d m L a) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d a U F) (hV : Rd_entry_d c V F) (hEV : M.mem E U)
    (hE : ∀ r, M.mem r E → Fn0_d m κ r) (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s)
    (hVD : IsFilter_d (ℳ := M) D V) : ∃ B, M.mem B V ∧
      ∀ s, M.mem s B ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
  classical
  by_cases refines : ∃ q, Fn0_d m n q ∧ Cp0_d m n L q c a
  · obtain ⟨q, hq, hqa⟩ := refines
    obtain ⟨B, hB, hu⟩ := hco m n q c a U V E hm hn hq hc hqa hV hU hE
    exact ⟨B, hu.mpr hEV, fun s => (hB s).trans
      (and_congr (hD s).symm (ec_ok_iff_l hZF.1 hc hinj hq hqa).symm)⟩
  · refine ⟨D, hVD.2.1, fun s => ⟨fun hs => ⟨hs, ?_⟩, And.left⟩⟩
    intro m' n' q hq hc' hqa
    have en := hc'.domain_eq_l hZF.1 hc
    subst n'
    have em := hqa.1.domain_eq_l hZF.1 ha
    subst m'
    exact (refines ⟨q, hq, hqa⟩).elim

def Ec_all_d (κ L A B n c s : M.Domain) : Prop := ∀ i a E, M.mem i n →
  Rd_entry_d i a A → Rd_entry_d i E B → Ec_ok_d κ L a c E s

def ec_all_m {d} (κ L A B n c s : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (.mem (.bound 2) n.weaken.weaken.weaken) (.imp (rd_entry_m (.bound 2) (.bound 1) A.weaken.weaken.weaken)
    (.imp (rd_entry_m (.bound 2) .newest B.weaken.weaken.weaken)
      (ec_ok_m κ.weaken.weaken.weaken L.weaken.weaken.weaken (.bound 1) c.weaken.weaken.weaken .newest s.weaken.weaken.weaken))))))
derive_free_closed ec_all_m

theorem ec_all_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L A B n c s : Term d) :
    Formula.satisfies ρ (ec_all_m κ L A B n c s) ↔
      Ec_all_d (κ.eval ρ) (L.eval ρ) (A.eval ρ) (B.eval ρ) (n.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [ec_all_m, Ec_all_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, ec_ok_sat_l hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
