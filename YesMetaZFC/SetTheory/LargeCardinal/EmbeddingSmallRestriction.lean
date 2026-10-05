import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite

/-! # 序数上的内部限制恢复整个小传递域上的限制

设 f:κ→B 是源内的实际枚举，B 传递。把 B 的关系码的像沿 j↾κ 回拉，
再在目标内塌缩，唯一性同时恢复 B 和 f。最后按 j(f)(j(α)) 计算 j(f(α))。
因此 j↾κ 属于目标就足以实际构造 j↾B，不预设整个嵌入图属于目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_small_restriction_l {ω κ K X R ξ K' Y S c d j p B f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω ξ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hp : M.mem p Y) (res : M.IsRestrictionOf I p j κ)
    (hB : M.TransitiveSet B) (hf : M.mem f X) (bij : M.IsSetBijectionFromTo I f κ B) :
    M.mem B Y ∧ ∃ k, M.mem k Y ∧ M.IsRestrictionOf I k j B := by
  have pf := fn0_of_function_l (ZF.modelsKP hZF)
    (res.isSetFunctionFromTo hj.1.1 (source.transitive κ source.cardinal_mem))
  have κY := sc_function_domain_mem_l hZF source.omega target.transitive hn target.theory hp pf
  obtain ⟨_, D, hDY, pd⟩ := sc_function_domain_l target.theory.algebra hp pf
  have pj a u (ha : Rd_entry_d a u p) := ((res.2 a u).mp ha).2
  obtain ⟨μ, hμ, hκμ⟩ := hj.1.1.2.2 κ source.cardinal_mem
  have pm : Fn0_d κ μ p := pf.retarget_l (fun a u ha =>
    ((hn.2 u μ).mp ((hj.relation_l I hZF source.omega hm.1 hn.1 (pj a u ha) hκμ).mp
      ((hm.2 a κ).mpr ⟨source.transitive κ source.cardinal_mem a (pf.bound_l ha).1, source.cardinal_mem, (pf.bound_l ha).1⟩))).2.2)
  have small := sc_small_pull_l hZF source.omega target.transitive hn target.theory κY hμ hp
    ((hj.small_l hZF source.omega source.transitive target.transitive hm hn hκμ).mp source.cardinal_small)
    ⟨fn0_function_l (ZF.modelsKP hZF) pm, fun a b u ha hb => hj.1.2 a b u (pj a u ha) (pj b u hb)⟩
  obtain ⟨K₀, ready⟩ := target.rebase_l hZF κY source.below small
  obtain ⟨P, hPY, product⟩ := ready.square_l hZF ready.cardinal_mem
  obtain ⟨T, hTX, bound, iso⟩ := ep_transitive_code_l hZF source hB hf bij
  obtain ⟨T', hT'Y, hTT⟩ := hj.1.1.2.2 T hTX
  -- 关系码可用 j↾κ 从其像直接回拉；全部量词都有目标内的实际界。
  let ρ : Env M 4 := ⟨Fin.cases κ (Fin.cases D (Fin.cases p (fun _ => T'))), fun _ => κ⟩
  let φ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (Formula.existsMem (.bound 4) (Formula.existsMem (.bound 5)
        (.conj (kpair0_m (.bound 4) (.bound 3) (.bound 2))
          (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 7))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 7)) (rd_entry0_m (.bound 1) .newest (.bound 8)))))))) }
  have sat q : φ.denote ρ q ↔ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧ ∃ u, M.mem u D ∧ ∃ v, M.mem v D ∧
      KPair_d M q a b ∧ Rd_entry_d a u p ∧ Rd_entry_d b v p ∧ Rd_entry_d u v T' := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨T₀, hT₀, spec⟩ := sc_separate_source_l I hZF source.omega target.transitive hn target.theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))
    ρ (Fin.cases κY (Fin.cases hDY (Fin.cases hp (fun _ => hT'Y)))) hPY
  have eq : T₀ = T := hZF.1.eq_of_same_members T₀ T (fun q => by
    rw [spec q, sat q]
    constructor
    · rintro ⟨_, a, _, b, _, u, _, v, _, hq, hau, hbv, huv⟩
      obtain ⟨r, hr, hrT⟩ := (hj.entry_l hZF source.omega source.transitive target.transitive hm hn
        (pj a u hau) (pj b v hbv) hTT).mpr huv
      exact kpair_unique_l M hZF.1 hr hq ▸ hrT
    · intro hqT
      obtain ⟨a, ha, b, hb, hq⟩ := bound q hqT
      obtain ⟨u, hu, hau⟩ := pd.2.1 a ha
      obtain ⟨v, hv, hbv⟩ := pd.2.1 b hb
      exact ⟨(product q).mpr ⟨a, ha, b, hb, hq⟩, a, ha, b, hb, u, hu, v, hv, hq, hau, hbv,
        (hj.entry_l hZF source.omega source.transitive target.transitive hm hn (pj a u hau) (pj b v hbv) hTT).mp ⟨q, hq, hqT⟩⟩)
  have hTY := eq ▸ hT₀
  obtain ⟨C, g, hCY, hgY, collapsed⟩ := target.collapse.collapse_l κY hTY small
    (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
  have hBY := (iso.unique_l hZF collapsed).symm ▸ hCY
  have hfY := (iso.graph_unique_l hZF collapsed).symm ▸ hgY
  -- 同一恢复也说明 B 在源中；其像和枚举的像由实际初等图给出。
  obtain ⟨C₀, g₀, hC₀, _, collapsed₀⟩ := source.collapse.collapse_l source.cardinal_mem hTX source.cardinal_small
    (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
  have hBX := (iso.unique_l hZF collapsed₀).symm ▸ hC₀
  obtain ⟨B', hB'Y, hBB⟩ := hj.1.1.2.2 B hBX
  obtain ⟨f', hf'Y, hff⟩ := hj.1.1.2.2 f hf
  have image := (hj.function_l hZF source.omega source.transitive target.transitive hm hn hκμ hBB hff).mp iso.function
  let η : Env M 5 := ⟨Fin.cases κ (Fin.cases D (Fin.cases f (Fin.cases p (fun _ => f')))), fun _ => κ⟩
  let ψ : BinarySchema 5 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m (.bound 1) (.bound 3) (.bound 6))
        (.conj (rd_entry0_m (.bound 1) .newest (.bound 7)) (rd_entry0_m .newest (.bound 2) (.bound 8))))) }
  have read x y : ψ.denote η x y ↔ ∃ a, M.mem a κ ∧ ∃ u, M.mem u D ∧
      Rd_entry_d a x f ∧ Rd_entry_d a u p ∧ Rd_entry_d u y f' := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨k, hkY, hk, select⟩ := sc_uniform_source_l hZF source.omega target.transitive hn target.theory ψ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))
    η (Fin.cases κY (Fin.cases hDY (Fin.cases hfY (Fin.cases hp (fun _ => hf'Y))))) hBY hB'Y (fun x hx => by
      obtain ⟨a, ha, hax⟩ := bij.2 x hx
      obtain ⟨u, hu, hau⟩ := pd.2.1 a ha
      obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x (source.transitive B hBX x hx)
      have huy := (hj.entry_l hZF source.omega source.transitive target.transitive hm hn (pj a u hau) hxy hff).mp hax
      exact ⟨y, (image.bound_l huy).2, (read x y).mpr ⟨a, ha, u, hu, hax, hau, huy⟩⟩)
  have entry x y (hxy : Rd_entry_d x y k) : Rd_entry_d x y j := by
    obtain ⟨a, _, u, _, hax, hau, huy⟩ := (read x y).mp (select x y hxy)
    obtain ⟨z, _, hxz⟩ := hj.1.1.2.2 x (source.transitive B hBX x (hk.bound_l hxy).1)
    have huz := (hj.entry_l hZF source.omega source.transitive target.transitive hm hn (pj a u hau) hxz hff).mp hax
    exact (fn0_function_l (ZF.modelsKP hZF) image).1.2 u z y huz huy ▸ hxz
  refine ⟨hBY, k, hkY, (fn0_function_l (ZF.modelsKP hZF) hk).1.1, fun x y => ⟨fun h => ⟨(hk.bound_l h).1, entry x y h⟩, ?_⟩⟩
  rintro ⟨hx, hxy⟩
  obtain ⟨z, _, hxz⟩ := hk.2.1 x hx
  exact hj.1.1.1.2 x z y (entry x z hxz) hxy ▸ hxz

end YesMetaZFC.SetTheory.LargeCardinal
