import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch

/-! # 源内有界代表及其求值图的传输

相对幂集和函数池由源量词刻画；节点的完备性则是有界陈述。
因此传输覆盖目标的全部合法代表，不要求目标中的代表逐个来自原源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.map_l {ω κ κ' L L' K K' X R Y S c d σ B B' J J' P P' G G' A A' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (hωX : M.mem ω X) (hκ : Rd_entry_d κ κ' σ) (hL : Rd_entry_d L L' σ) (hK : Rd_entry_d K K' σ)
    (hB : Rd_entry_d B B' σ) (hJ : Rd_entry_d J J' σ) (hP : Rd_entry_d P P' σ)
    (hG : Rd_entry_d G G' σ) (hA : Rd_entry_d A A' σ) (pool : Eb_pool_d ω κ L X B J K P G A) :
    Eb_pool_d ω κ' L' Y B' J' K' P' G' A' := by
  have ωσ := hσ.omega_l I hZF hω hX hY hm hn hωX
  have out {a b} (h : Rd_entry_d a b σ) : M.mem b Y := hσ.1.1.output_mem_of_pairMember h
  refine ⟨out hJ, out hP, out hG, out hA, ?_, ?_, ?_⟩
  · exact hσ.power_l hZF hω hX hY hm hn hK hP pool.subsets
  · let φ : Formula 1 4 := .iff (.mem .newest (.bound 1))
      (Formula.forallMem .newest (Formula.existsMem (.bound 3) (Formula.existsMem (.bound 5)
        (kpair0_m (.bound 2) (.bound 1) .newest))))
    have tr := hσ.forall_delta_l hZF hω hX hY hm hn φ
      (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
      (.iff (.mem ..) (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))))
      ⟨Fin.cases G (Fin.cases K (fun _ => B)), fun _ => B⟩
      ⟨Fin.cases G' (Fin.cases K' (fun _ => B')), fun _ => B'⟩ (Fin.cases hG (Fin.cases hK (fun _ => hB)))
    simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
    have read := tr.mp (fun f hf => (pool.graphs f).trans ⟨And.right, fun hs => ⟨hf, hs⟩⟩)
    exact fun f => ⟨fun hf => ⟨hY G' (out hG) f hf, (read f (hY G' (out hG) f hf)).mp hf⟩,
      fun ⟨hf, hs⟩ => (read f hf).mpr hs⟩
  · -- 有界的生成条款把目标中每个合法支撑与函数配成节点。
    let φ : Formula 1 9 := .conj
      (Formula.forallMem .newest (eb_node_m (.bound 9) (.bound 8) (.bound 7) (.bound 6)
        (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))
      (Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3) (Formula.forallMem (.bound 10)
        (Formula.forallMem (.bound 4) (.imp
          (.conj (fn0_m (.bound 1) (.bound 10) (.bound 3))
            (.conj (eb_space_m (.bound 11) (.bound 9) (.bound 1) .newest) (fn0_m .newest (.bound 8) (.bound 2))))
          (Formula.existsMem (.bound 4) (kpair0_m .newest (.bound 4) (.bound 3))))))))
    have tr := smap_delta_l I hZF hω hX hY hm hn hσ φ
      (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
      (.conj (.forallMem _ (eb_node_delta_l ..)) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (.conj (fn0_delta_l ..) (.conj (eb_space_delta_l ..) (fn0_delta_l ..)))
          (.existsMem _ (kpair0_delta_l ..))))))))
      ⟨Fin.cases A (Fin.cases P (Fin.cases G (Fin.cases J (Fin.cases B (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω)))))))), fun _ => ω⟩
      ⟨Fin.cases A' (Fin.cases P' (Fin.cases G' (Fin.cases J' (Fin.cases B' (Fin.cases K' (Fin.cases L' (Fin.cases κ' (fun _ => ω)))))))), fun _ => ω⟩
      (Fin.cases hA (Fin.cases hP (Fin.cases hG (Fin.cases hJ (Fin.cases hB (Fin.cases hK (Fin.cases hL (Fin.cases hκ (fun _ => ωσ)))))))))
    simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_existsMem_iff, eb_node_sat_l hZF.1, eb_space_sat_l hZF.1, fn0_sat_l hZF.1, kpair0_sat_l hZF.1] at tr
    have read := tr.mp ⟨fun u hu => (pool.nodes u).mp hu, fun a ha f hf n hn D hd h => by
      obtain ⟨u, pair⟩ := (I).total a f
      exact ⟨u, (pool.nodes u).mpr ⟨a, ha, f, hf, pair, n, hn, D, hd, h⟩, pair⟩⟩
    intro u
    refine ⟨read.1 u, ?_⟩
    rintro ⟨a, ha, f, hf, pair, n, hn, D, hd, ff, space, gf⟩
    obtain ⟨v, hv, pair'⟩ := read.2 a ha f hf n hn D hd ⟨ff, space, gf⟩
    exact kpair_unique_l M hZF.1 pair' pair ▸ hv

/-- 全部节点、原测度关系与递归求值方程一同传输，保留给定求值图的实际像。 -/
theorem Eb_collapse_d.map_l {ω κ κ' L L' K K' X R Y S c d σ B B' F F' A A' Q Q' Z Z' e e' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (theory : Sc_theory_d I ω Y S) (hωX : M.mem ω X)
    (hκ : Rd_entry_d κ κ' σ) (hL : Rd_entry_d L L' σ) (hK : Rd_entry_d K K' σ)
    (hB : Rd_entry_d B B' σ) (hF : Rd_entry_d F F' σ) (hA : Rd_entry_d A A' σ)
    (hQ : Rd_entry_d Q Q' σ) (hZ : Rd_entry_d Z Z' σ) (he : Rd_entry_d e e' σ)
    (collapse : Eb_collapse_d ω κ L K X B F A Q Z e) : Eb_collapse_d ω κ' L' K' Y B' F' A' Q' Z' e' := by
  obtain ⟨J, P, G, U, V, pool, indices, hU, hV, _, _, range, membership, shape, edges, wc, member⟩ := collapse
  obtain ⟨J', _, hJ⟩ := hσ.1.1.2.2 J pool.indices
  obtain ⟨P', _, hP⟩ := hσ.1.1.2.2 P pool.powers
  obtain ⟨G', _, hG⟩ := hσ.1.1.2.2 G pool.functions
  obtain ⟨U', hU', hUU⟩ := hσ.1.1.2.2 U hU
  obtain ⟨V', hV', hVV⟩ := hσ.1.1.2.2 V hV
  have ωσ := hσ.omega_l I hZF hω hX hY hm hn hωX
  have pool' := pool.map_l hZF hω hX hY hm hn hσ hωX hκ hL hK hB hJ hP hG hA
  have indices' := ep_indices_map_l hZF hω hX hY hm hn hσ theory hωX hL hJ indices
  have shape' : ∀ p, M.mem p Q' → ∃ u, M.mem u A' ∧ ∃ v, M.mem v A' ∧ KPair_d M p u v := by
    let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
      (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
    have tr := smap_delta_l I hZF hω hX hY hm hn hσ φ
      (by simp -implicitDefEqProofs [φ])
      (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
      ⟨Fin.cases Q (fun _ => A), fun _ => A⟩ ⟨Fin.cases Q' (fun _ => A'), fun _ => A'⟩ (Fin.cases hQ (fun _ => hA))
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
    exact tr.mp shape
  have wc' : Wc_map_d A' Q' Z' e' := by
    have tr := smap_delta_l I hZF hω hX hY hm hn hσ (n := 4)
      (wc_map_m (.bound 3) (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (wc_map_delta_l ..)
      ⟨Fin.cases e (Fin.cases Z (Fin.cases Q (fun _ => A))), fun _ => A⟩
      ⟨Fin.cases e' (Fin.cases Z' (Fin.cases Q' (fun _ => A'))), fun _ => A'⟩
      (Fin.cases he (Fin.cases hZ (Fin.cases hQ (fun _ => hA))))
    simp only [wc_map_sat_l hZF.1] at tr
    exact tr.mp wc
  refine ⟨J', P', G', U', V', pool', indices', hU', hV', hσ.1.1.output_mem_of_pairMember hQ,
    hσ.1.1.output_mem_of_pairMember he, ?_, ?_, shape', ?_, wc', ?_⟩
  · have tr := smap_delta_l I hZF hω hX hY hm hn hσ (n := 2)
      (rd_graph_m .range (.bound 1) (.bound 1) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (rd_graph_delta_l ..)
      ⟨Fin.cases U (fun _ => F), fun _ => F⟩ ⟨Fin.cases U' (fun _ => F'), fun _ => F'⟩ (Fin.cases hUU (fun _ => hF))
    simp only [rd_graph_sat_l (ZF.modelsKP hZF)] at tr
    exact tr.mp range
  · have tr := smap_delta_l I hZF hω hX hY hm hn hσ (n := 2)
      (rd_graph_m .mem (.bound 1) (.bound 1) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (rd_graph_delta_l ..)
      ⟨Fin.cases V (fun _ => B), fun _ => B⟩ ⟨Fin.cases V' (fun _ => B'), fun _ => B'⟩ (Fin.cases hVV (fun _ => hB))
    simp only [rd_graph_sat_l (ZF.modelsKP hZF)] at tr
    exact tr.mp membership
  · let φ : Formula 1 12 := Formula.forallMem (.bound 1) (Formula.forallMem (.bound 2)
      (.iff (rd_entry0_m (.bound 1) .newest (.bound 2))
        (eb_link_m (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
          (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)))
    have tr := smap_delta_l I hZF hω hX hY hm hn hσ φ
      (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
      (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (eb_link_delta_l ..))))
      ⟨Fin.cases Q (Fin.cases A (Fin.cases G (Fin.cases F (Fin.cases V (Fin.cases U
        (Fin.cases K (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases κ (fun _ => ω))))))))))), fun _ => ω⟩
      ⟨Fin.cases Q' (Fin.cases A' (Fin.cases G' (Fin.cases F' (Fin.cases V' (Fin.cases U'
        (Fin.cases K' (Fin.cases J' (Fin.cases B' (Fin.cases L' (Fin.cases κ' (fun _ => ω))))))))))), fun _ => ω⟩
      (Fin.cases hQ (Fin.cases hA (Fin.cases hG (Fin.cases hF (Fin.cases hVV (Fin.cases hUU
        (Fin.cases hK (Fin.cases hJ (Fin.cases hB (Fin.cases hL (Fin.cases hκ (fun _ => ωσ))))))))))))
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      rd_entry0_sat_l hZF.1, eb_link_sat_l hZF.1] at tr
    have read := tr.mp (fun u hu v hv => (edges u v).trans ⟨fun h => h.2.2, fun h => ⟨hu, hv, h⟩⟩)
    intro u v
    refine ⟨fun h => ?_, fun ⟨hu, hv, h⟩ => (read u hu v hv).mpr h⟩
    obtain ⟨p, pair, hp⟩ := h
    obtain ⟨a, ha, b, hb, pair'⟩ := shape' p hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact ⟨ha, hb, (read a ha b hb).mp ⟨p, pair, hp⟩⟩
  · -- 重复代表也完整反映成员关系；此条款随原求值图一起传输。
    let φ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 4)
      (Formula.forallMem (.bound 3) (Formula.forallMem (.bound 4)
        (.imp (rd_entry0_m (.bound 3) (.bound 1) (.bound 4))
          (.imp (rd_entry0_m (.bound 2) .newest (.bound 4))
            (.iff (rd_entry0_m (.bound 3) (.bound 2) (.bound 6)) (.mem (.bound 1) .newest)))))))
    have tr := smap_delta_l I hZF hω hX hY hm hn hσ φ
      (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
      (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.iff (rd_entry0_delta_l ..) (.mem ..))))))))
      ⟨Fin.cases e (Fin.cases Z (Fin.cases Q (fun _ => A))), fun _ => A⟩
      ⟨Fin.cases e' (Fin.cases Z' (Fin.cases Q' (fun _ => A'))), fun _ => A'⟩
      (Fin.cases he (Fin.cases hZ (Fin.cases hQ (fun _ => hA))))
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff] at tr
    have read := tr.mp (fun u _ v _ x _ y _ => member u v x y)
    exact fun u v x y hu hv => read u (wc'.function.bound_l hu).1 v (wc'.function.bound_l hv).1
      x (wc'.function.bound_l hu).2 y (wc'.function.bound_l hv).2 hu hv

end YesMetaZFC.SetTheory.LargeCardinal
