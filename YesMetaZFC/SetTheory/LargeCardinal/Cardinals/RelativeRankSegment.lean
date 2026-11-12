import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingSetImage
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ξ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hp : M.mem p Y) (res : M.IsRestrictionOf I p j κ)
    (hB : M.TransitiveSet B) (hf : M.mem f X) (bij : M.IsSetBijectionFromTo I f κ B) :
    M.mem B Y ∧ ∃ k, M.mem k Y ∧ M.IsRestrictionOf I k j B := by
  have pf := fn0_of_function_l (ZF.modelsKP hZF)
    (res.isSetFunctionFromTo hj.1.1 (source.transitive κ source.cardinal_mem))
  have κY := sc_function_domain_mem_l hZF source.omega target.transitive hn target.theory hp pf
  obtain ⟨_, D, hDY, pd⟩ := sc_function_domain_l (target.algebra_l (ZF.modelsKP hZF)) hp pf
  have pj a u (ha : Rd_entry_d a u p) := ((res.2 a u).mp ha).2
  obtain ⟨μ, hμ, hκμ⟩ := hj.1.1.2.2 κ source.cardinal_mem
  have pm : Fn0_d κ μ p := pf.retarget_l (fun a u ha =>
    ((hn.2 u μ).mp ((hj.relation_l I hZF source.omega hm.1 hn.1 (pj a u ha) hκμ).mp
      ((hm.2 a κ).mpr ⟨source.transitive κ source.cardinal_mem a (pf.bound_l ha).1, source.cardinal_mem, (pf.bound_l ha).1⟩))).2.2)
  have small := sc_small_pull_l hZF source.omega target.transitive hn target.theory κY hμ hp
    ((rf_small_mem_l I (ZF.modelsKP hZF) target.transitive hn hμ).mp
      ((hj.small_l I hZF source.omega hm.1 hn.1 hκμ).mp source.cardinal_small))
    ⟨fn0_function_l (ZF.modelsKP hZF) pm, fun a b u ha hb => hj.1.2 a b u (pj a u ha) (pj b u hb)⟩
  obtain ⟨K₀, ready⟩ := target.rebase_l κY source.below ((rf_small_mem_l I (ZF.modelsKP hZF) target.transitive hn κY).mpr small)
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
  obtain ⟨C, g, hCY, hgY, collapsed⟩ := target.collapse.collapse_l I (ZF.modelsKP hZF) target.transitive hn κY hTY small
    (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
  have hBY := (iso.unique_l hZF collapsed).symm ▸ hCY
  have hfY := (iso.graph_unique_l hZF collapsed).symm ▸ hgY
  -- 同一恢复也说明 B 在源中；其像和枚举的像由实际初等图给出。
  obtain ⟨C₀, g₀, hC₀, _, collapsed₀⟩ := source.collapse.collapse_l I (ZF.modelsKP hZF) source.transitive hm source.cardinal_mem hTX (source.cardinal_small_l (ZF.modelsKP hZF))
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

/-! ## 不可达秩段上的实际限制图

任意传递源可通过已有真实枚举调用小域恢复。这里另外从正则 Hχ 源和
不可达 κ 自动构造 κ→Vκ 的枚举及其源内成员资格，消除该实例的枚举输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 严格相对秩段的像及其完整初等限制同时构造，目标高度保留内部正则性。 -/
theorem ep_rank_restriction_l (hZF : M.Models ZF)
    {ω κ K X R μ K' Y S c d j a A Q α β : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hA : M.mem A X) (rank : Vr_d X α A) (regular : Sc_regular_d X α)
    (ha : Smem_d (kp_pair_l (ZF.modelsKP hZF)) a A Q) (hαβ : Rd_entry_d α β j) :
    ∃ B b T p, M.mem B Y ∧ Vr_d Y β B ∧ Sc_regular_d Y β ∧ Rd_entry_d A B j ∧
      Smem_d (kp_pair_l (ZF.modelsKP hZF)) b B T ∧
      M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) p j A ∧ Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω a b A B p := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB, hAB⟩ := hj.1.1.2.2 A hA
  obtain ⟨x, hx⟩ := ha.1.2.1
  obtain ⟨y, hy, hxy⟩ := hj.1.1.2.2 x (source.transitive A hA x hx)
  have hyB := ((hn.2 y B).mp ((hj.relation_l I hZF source.omega hm.1 hn.1 hxy hAB).mp
    ((hm.2 x A).mpr ⟨source.transitive A hA x hx, hA, hx⟩))).2.2
  obtain ⟨b, T, code⟩ := smdl_membership_l I hZF ⟨y, hyB⟩
  obtain ⟨p, res, elem⟩ := ep_set_restriction_l hZF source target hm hn hj ha.1 code.1 hAB
    (ep_set_membership_l hZF source target hm hn hj ha code hAB)
  exact ⟨B, b, T, p, hB, (hj.hierarchy_l hZF source.omega source.transitive target.transitive hm hn hαβ hAB).mp rank,
    (hj.regular_l hZF source.omega source.transitive target.transitive hm hn hαβ).mp regular, hAB, code, res, elem⟩

theorem ep_h_rank_enumeration_l (hZFC : M.Models ZFC) {ω χ X κ B : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X)
    (hκX : M.mem κ X) (hωκ : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ B) :
    ∃ f, M.mem f X ∧ M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) f κ B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨f, hf⟩ := ZFC.inaccessible_enumeration_l I hZFC hω hωκ hr hs hB
  obtain ⟨μ, hμ, g, hg⟩ := ZF.hmem_size_l I hZF ((hX κ).mp hκX)
  obtain ⟨r, hr'⟩ := ZF.exists_inverseBijection hZF I hf
  have hBX := (hX B).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal
    (v_transitive_l I hB) (fun _ h => h) hμ (ZF.exists_compositionInjection hZF I hr'.1 hg))
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hX hκX
    (hf.1.1.mono_target_l I (ZF.h_transitive_l I hZF hX B hBX)), hf⟩

theorem smap_h_rank_restriction_l (hZFC : M.Models ZFC)
    {ω κ K X R ξ K' Y S c d j p χ B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω ξ K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d X Y j)
    (hp : M.mem p Y) (res : M.IsRestrictionOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p j κ)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X) (hωκ : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ B) : M.mem B Y ∧
      ∃ k, M.mem k Y ∧ M.IsRestrictionOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) k j B := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨f, hf, bij⟩ := ep_h_rank_enumeration_l hZFC source.omega hχ hωχ hX source.cardinal_mem hωκ hr hs hB
  exact smap_small_restriction_l hZF source target hm hn hj hp res
    (v_transitive_l (kp_pair_l (ZF.modelsKP hZF)) hB) hf bij

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可沿迭代传输的相对秩层枚举

初始 Vδ 中的不可达层有实际 κ 枚举；把枚举记录为有界塌缩证书后，
初等像仍带源内枚举，不要求像序数在背景中不可达或不可数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Er_level_d (X κ B : M.Domain) : Prop where
  member : M.mem B X
  hierarchy : Vr_d X κ B
  code : ∃ T f, M.mem T X ∧ M.mem f X ∧ Wc_iso_d κ T B f

theorem ep_relative_rank_l (hZFC : M.Models ZFC) {ω κ K X R δ L B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (hL : M.mem L δ) (hωL : M.mem ω L)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L B) : Er_level_d X L B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hLX := ZF.v_ordinal_mem_l I hZF hX hL
  have hBX := ZF.v_mem_l I hZF hB hX hL
  obtain ⟨f, hf⟩ := ZFC.inaccessible_enumeration_l I hZFC source.omega hωL hr hs hB
  obtain ⟨D, hDX, hLD, hBD⟩ := v_joint_bound_l I hX hLX hBX
  have hfX := v_relation_mem_l I hX hδ hDX (F := f) (fun p hp => by
    obtain ⟨a, ha, b, hb, hab⟩ := (fn0_of_function_l (ZF.modelsKP hZF) hf.1.1).1 p hp
    exact ⟨a, hLD a ha, b, hBD b hb, hab⟩)
  obtain ⟨T, hTX, _, iso⟩ := ep_transitive_code_l hZF source (v_transitive_l I hB) hfX hf
  obtain ⟨C, F, hCX, hFX, cert, _⟩ := vr_source_l hZF hX hδ hL hB
  exact ⟨hBX, ⟨C, F, hCX, hFX, fun t _ => cert t⟩, T, f, hTX, hfX, iso⟩

/-- 同时传输秩递归历史和实际枚举，保留非标准内部序数上的枚举资格。 -/
theorem Er_level_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ ℓ B C : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hκ : Rd_entry_d κ ℓ j) (hB : Rd_entry_d B C j) (h : Er_level_d X κ B) : Er_level_d Y ℓ C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨T, f, hT, hf, iso⟩ := h.code
  obtain ⟨T', hT', hTT⟩ := hj.1.1.2.2 T hT
  obtain ⟨f', hf', hff⟩ := hj.1.1.2.2 f hf
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 4)
    (wc_iso_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (wc_iso_delta_l ..)
    ⟨Fin.cases f (Fin.cases B (Fin.cases T (fun _ => κ))), fun _ => κ⟩
    ⟨Fin.cases f' (Fin.cases C (Fin.cases T' (fun _ => ℓ))), fun _ => ℓ⟩
    (Fin.cases hff (Fin.cases hB (Fin.cases hTT (fun _ => hκ))))
  exact ⟨hj.1.1.output_mem_of_pairMember hB, (hj.hierarchy_l hZF hω hX hY hm hn hκ hB).mp h.hierarchy,
    T', f', hT', hf', (wc_iso_sat_l hZF.1 ..).mp (tr.mp ((wc_iso_sat_l hZF.1 ..).mpr iso))⟩

/-- 同一秩层和枚举图进入严格截断；关系码在截断源中由原枚举重新分离。 -/
theorem Er_level_d.rank_l (hZF : M.Models ZF) {ω μ K X α V R κ B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K V R) (hX : M.TransitiveSet X) (hV : M.mem V X)
    (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V)
    (h : Er_level_d X κ B) : Er_level_d V κ B := by
  obtain ⟨hB, hierarchy⟩ := rank.rank_l hZF hX hV hα hκ h.member h.hierarchy
  obtain ⟨_, f, _, hf, iso⟩ := h.code
  have hfV := rank.relation_mem_l hX hV hα hκ hB hf iso.function.1
  obtain ⟨T, hT, _, code⟩ := ep_transitive_code_l hZF source iso.transitive hfV (iso.bijection_l (ZF.modelsKP hZF))
  exact ⟨hB, hierarchy, T, f, hT, hfV, code⟩

/-- 自动读取已经装配的相对秩层枚举，将序数限制恢复为整个秩层的限制。 -/
theorem Er_level_d.restriction_l (hZF : M.Models ZF)
    {ω κ K X R ξ K' Y S c d j p B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ξ K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hp : M.mem p Y) (res : M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) p j κ)
    (h : Er_level_d X κ B) : M.mem B Y ∧
      ∃ k, M.mem k Y ∧ M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) k j B := by
  obtain ⟨_, f, _, hf, iso⟩ := h.code
  exact smap_small_restriction_l hZF source target hm hn hj hp res iso.transitive hf
    (iso.bijection_l (ZF.modelsKP hZF))

end YesMetaZFC.SetTheory.LargeCardinal
