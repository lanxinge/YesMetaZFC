import YesMetaZFC.SetTheory.LargeCardinal.FiniteSupport
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 派生测度的实际坐标投影

先证明临界点以下序数间的内部函数逐点固定，再构造 p(s)=s∘q。
其有界定义传到目标，给出 j(p)(a)=a∘q；全程允许内部非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_small_function_fixed_l (hZF : M.Models ZF) {ω δ X C Y E j κ k m n q}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hm : M.mem m κ) (hn : M.mem n κ) (hq : Fn0_d m n q) : M.PairMember I q q j := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hqX := ZF.v_relation_mem_l I hZF hX hδ hc.source (F := q) (fun p hp => by
    obtain ⟨i, hi, r, hr, hp⟩ := hq.1 p hp
    exact ⟨i, hc.ordinal.transitive m hm i hi, r, hc.ordinal.transitive n hn r hr, hp⟩)
  obtain ⟨q', _, hjq⟩ := hj.2.2 q hqX
  have hq' := (spred_function_l I hZF hω h ht hY (hc.fixed m hm) (hc.fixed n hn) hjq).mp hq
  have eq := hq.ext_l hZF.1 hq' (fun i hi => by
    obtain ⟨r, hr, hir⟩ := hq.2.1 i hi
    exact ⟨r, hir, (spred_entry_l I hZF hω h ht hY
      (hc.fixed i (hc.ordinal.transitive m hm i hi)) (hc.fixed r (hc.ordinal.transitive n hn r hr)) hjq).mp hir⟩)
  exact eq.symm ▸ hjq

/-- 投影及其像均实际存在；像投影在任意目标支撑上执行同一坐标重排。 -/
theorem ed_reindex_l (hZF : M.Models ZF) {ω δ X C Y E j κ k m n q H D L a b}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hm : M.mem m κ) (hn : M.mem n κ) (hq : Fn0_d m n q)
    (hH : ∀ s, M.mem s H ↔ Fn0_d n κ s) (hD : ∀ t, M.mem t D ↔ Fn0_d m κ t)
    (hL : M.MemberSubset L k) (haY : M.mem a Y) (hbY : M.mem b Y) (ha : Fn0_d n L a)
    (hb : Cp0_d m n L q a b) : ∃ H' D' p p', M.PairMember I H H' j ∧ M.PairMember I D D' j ∧ Fn0_d H D p ∧
      (∀ s t, Rd_entry_d s t p ↔ M.mem s H ∧ Cp0_d m n κ q s t) ∧
      M.PairMember I p p' j ∧ Rd_entry_d a b p' := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hjq := ed_small_function_fixed_l I hZF hω hX hδ h hY hc hm hn hq
  obtain ⟨R, hRX, hR⟩ := ZF.v_relation_cover_l I hZF hX hδ hc.source
  have bound {l s} (hl : M.mem l κ) (hs : Fn0_d l κ s) : M.mem s R :=
    hR s fun p hp => (hs.1 p hp).elim fun i hi => hi.2.elim fun r hr =>
      ⟨i, hc.ordinal.transitive l hl i hi.1, r, hr⟩
  have space {l T} (hl : M.mem l κ) (hT : ∀ s, M.mem s T ↔ Fn0_d l κ s) : M.mem T X := by
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF R
    exact ht P (ZF.v_power_mem_l I hZF hX hδ hRX hP) T ((hP T).mpr fun s hs => bound hl ((hT s).mp hs))
  obtain ⟨H', _, hjH⟩ := hj.2.2 H (space hn hH)
  obtain ⟨D', _, hjD⟩ := hj.2.2 D (space hm hD)
  obtain ⟨p, hp, spec⟩ := cp0_projection_l (ZF.modelsKP hZF) hq hH hD
  have hpX := ZF.v_relation_mem_l I hZF hX hδ hRX (F := p) (fun r hr => by
    obtain ⟨s, hs, t, ht, hr⟩ := hp.1 r hr
    exact ⟨s, bound hn ((hH s).mp hs), t, bound hm ((hD t).mp ht), hr⟩)
  obtain ⟨p', _, hjp⟩ := hj.2.2 p hpX
  let φ : Formula 1 7 := Formula.forallMem (.bound 2) (Formula.forallMem (.bound 2)
    (.iff (rd_entry0_m (.bound 1) .newest (.bound 2))
      (cp0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest)))
  have tr := spred_delta_l I hZF hω h ht hY φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (cp0_delta_l ..))))
    ⟨Fin.cases p (Fin.cases D (Fin.cases H (Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m)))))), fun _ => m⟩
    ⟨Fin.cases p' (Fin.cases D' (Fin.cases H' (Fin.cases q (Fin.cases k (Fin.cases n (fun _ => m)))))), fun _ => m⟩
    (Fin.cases hjp (Fin.cases hjD (Fin.cases hjH (Fin.cases hjq (Fin.cases hc.image (Fin.cases (hc.fixed n hn)
      (fun _ => hc.fixed m hm)))))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1, cp0_sat_l hZF.1] at tr
  have target := tr.mp (fun s hs t _ => (spec s t).trans ⟨And.right, fun h => ⟨hs, h⟩⟩)
  have haH := es_seed_l I hZF hω h ht hY (hc.fixed n hn) hc.image hjH hH hL haY ha
  have hbD := es_seed_l I hZF hω h ht hY (hc.fixed m hm) hc.image hjD hD hL hbY hb.1
  exact ⟨H', D', p, p', hjH, hjD, hp, spec, hjp, (target a haH b hbD).mpr (cp0_mono_l hL hb)⟩

end YesMetaZFC.SetTheory.LargeCardinal
