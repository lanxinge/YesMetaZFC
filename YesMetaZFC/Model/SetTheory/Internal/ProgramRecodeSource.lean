import YesMetaZFC.Model.SetTheory.Internal.ProgramRecodeSemantics
import YesMetaZFC.Model.SetTheory.Internal.CanonicalSource

/-! # 原程序到平坦程序的转换证书在极限秩层中绝对

输入坐标由 Kuratowski 码回收，输出坐标由平坦配对的秩界回收。
源只承担实际秩闭包，不承担背景的整个集合论。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {ω δ Z : M.Domain}
  (hω : M.IsOmega ω) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (hωZ : M.mem ω Z)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => ZF.v_transitive_l I hZF hV

include hω hV hωZ in
theorem Sx_node_d.rank_mem_l {c d} (h : Sx_node_d I K c d) (hc : M.mem c Z) : M.mem d Z := by
  obtain ⟨k, p, i, j, q, hc', hp, hq, hd⟩ := h
  have kp := hc'.mem_l M T hc
  have ij := hp.mem_l M T kp.2
  have hωδ := (v_ordinal_l I hV).transitive ω (ZF.v_ordinal_height_l hZF hV (hω.isOrdinal hZF) hωZ)
  have hqZ := ((fp_fixed_l hZF.1 hω).mp hq).rank_mem_l I hZF hω hV hωδ ij.1 ij.2
  exact ((fp_fixed_l hZF.1 hω).mp hd).rank_mem_l I hZF hω hV hωδ kp.1 hqZ

variable (hδ : M.IsLimitOrdinal δ)
local notation "nz" => Nonempty.intro (Subtype.mk ω hωZ)
local notation "P" => sc_v_pair_l hZF hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P
local notation "L" => fp_rank_interpretation_l I hZF hω hV hωZ

theorem rt_sx_node_l (c d : (N).Domain) : Sx_node_d J L c d ↔ Sx_node_d I K c.val d.val := by
  have code := rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  constructor
  · rintro ⟨k, p, i, j, q, hc, hp, hq, hd⟩
    exact ⟨k.val, p.val, i.val, j.val, q.val, (code ..).mp hc, (code ..).mp hp,
      (fp_fixed_l hZF.1 hω).mpr hq, (fp_fixed_l hZF.1 hω).mpr hd⟩
  · rintro ⟨k, p, i, j, q, hc, hp, hq, hd⟩
    have kp := hc.mem_l M T c.property
    have ij := hp.mem_l M T kp.2
    have kq := ((fp_fixed_l hZF.1 hω).mp hd).inverse_rank_l I hZF hω.1 hV d.property
    exact ⟨⟨k, kp.1⟩, ⟨p, kp.2⟩, ⟨i, ij.1⟩, ⟨j, ij.2⟩, ⟨q, kq.2⟩,
      (code ..).mpr hc, (code ..).mpr hp, (fp_fixed_l hZF.1 hω).mp hq, (fp_fixed_l hZF.1 hω).mp hd⟩

theorem rt_sx_program_l (F G : (N).Domain) :
    Sx_program_d J L F G ↔ Sx_program_d I K F.val G.val := by
  have ent := rt_entry_l T nz hZF.1
  have flat := rt_fp_entry_l I hZF hω hV hωZ
  refine and_congr (rt_fp_function_l I hZF hω hV hωZ G) ?_
  constructor
  · intro h r d
    constructor
    · intro hrd
      have rd := rt_fp_coordinates_l I hZF hω hV G.property hrd
      obtain ⟨c, hc, code⟩ := (h ⟨r, rd.1⟩ ⟨d, rd.2⟩).mp ((flat ..).mpr hrd)
      exact ⟨c.val, (ent ..).mp hc, (rt_sx_node_l hZF hω hV hωZ hδ ..).mp code⟩
    · rintro ⟨c, hc, code⟩
      have rc := rd_entry_transitive_l T F.property hc
      let r' : (N).Domain := ⟨r, rc.1⟩
      let c' : (N).Domain := ⟨c, rc.2⟩
      let d' : (N).Domain := ⟨d, code.rank_mem_l hZF hω hV hωZ rc.2⟩
      exact (flat ..).mp ((h r' d').mpr
        ⟨c', (ent ..).mpr hc, (rt_sx_node_l hZF hω hV hωZ hδ c' d').mpr code⟩)
  · intro h r d
    refine (flat r d G).trans ((h r.val d.val).trans ?_)
    constructor
    · rintro ⟨c, hc, code⟩
      let c' : (N).Domain := ⟨c, (rd_entry_transitive_l T F.property hc).2⟩
      exact ⟨c', (ent ..).mpr hc, (rt_sx_node_l hZF hω hV hωZ hδ c' d).mpr code⟩
    · rintro ⟨c, hc, code⟩
      exact ⟨c.val, (ent ..).mp hc, (rt_sx_node_l hZF hω hV hωZ hδ c d).mp code⟩

end YesMetaZFC.SetTheory.Internal
