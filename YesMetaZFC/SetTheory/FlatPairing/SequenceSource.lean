import YesMetaZFC.SetTheory.FlatPairing.Functions
import YesMetaZFC.SetTheory.FlatPairing.RankObjects

/-! # 前缀编码在包含对象层的任意秩层中绝对

轨道的每一个量化坐标都由实际函数图回收。反向存在性直接使用图的秩界，
因此前缀编码公式在 V(ν+1) 中解释的正是背景中的编码关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem rt_fs_trace_l (A f H : (N).Domain) :
    Fs_trace_d J ⟨ω, hωY⟩ A f H ↔ Fs_trace_d K ω A.val f.val H.val := by
  have trans := v_transitive_l I hW
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have fn := rt_fp_function_from_l I hZF hω hW hωY H ⟨ω, hωY⟩ A
  have successor := rt_successor_l trans (Nonempty.intro (Subtype.mk ω hωY)) hZF.1
  constructor
  · rintro ⟨hH, zero, step⟩
    refine ⟨fn.mp hH, ?_, ?_⟩
    · intro z hz
      obtain ⟨e, he, heω⟩ := hω.1.1
      have hzω := hZF.1.eq_of_same_members e z (fun x => iff_of_false (he x) (hz x)) ▸ heω
      let z' : (N).Domain := ⟨z, trans ω hωY z hzω⟩
      exact (entry z' z' H).mp (zero z' (fun x => hz x.val))
    · intro i j p q x succ hp hq hx
      have ip := rt_fp_coordinates_l I hZF hω hW H.property hp
      have jq := rt_fp_coordinates_l I hZF hω hW H.property hq
      have ix := rt_fp_coordinates_l I hZF hω hW f.property hx
      let i' : (N).Domain := ⟨i, ip.1⟩
      let j' : (N).Domain := ⟨j, jq.1⟩
      let p' : (N).Domain := ⟨p, ip.2⟩
      let q' : (N).Domain := ⟨q, jq.2⟩
      let x' : (N).Domain := ⟨x, ix.2⟩
      exact (fp_fixed_l hZF.1 hω).mpr (step i' j' p' q' x' ((successor j' i').mpr succ)
        ((entry i' p' H).mpr hp) ((entry j' q' H).mpr hq) ((entry i' x' f).mpr hx))
  · rintro ⟨hH, zero, step⟩
    refine ⟨fn.mpr hH, ?_, ?_⟩
    · intro z hz
      exact (entry z z H).mpr (zero z.val (fun x hx => hz ⟨x, trans z.val z.property x hx⟩ hx))
    · intro i j p q x succ hp hq hx
      exact (fp_fixed_l hZF.1 hω).mp (step i.val j.val p.val q.val x.val ((successor j i).mp succ)
        ((entry i p H).mp hp) ((entry j q H).mp hq) ((entry i x f).mp hx))

/-- 整条轨道是 A 的子集，确实属于当前外层，故不是仅有外向蕴含的相对化。 -/
theorem rt_fs_code_l (A f n p : (N).Domain) {ν : M.Domain}
    (hV : V_d I ν A.val) (hων : M.MemberSubset ω ν) :
    Fs_code_d J ⟨ω, hωY⟩ A f n p ↔ Fs_code_d K ω A.val f.val n.val p.val := by
  have trace := rt_fs_trace_l I hZF hω hW hωY A f
  have entry := rt_fp_entry_l I hZF hω hW hωY n p
  constructor
  · rintro ⟨H, hH, hp⟩
    exact ⟨H.val, (trace H).mp hH, (entry H).mp hp⟩
  · rintro ⟨H, hH, hp⟩
    have bound := fp_function_rank_l I hZF hω hV hων
      (fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi)) hH.1
    let H' : (N).Domain := ⟨H, v_subset_mem_l I hW A.property bound⟩
    exact ⟨H', (trace H').mpr hH, (entry H').mpr hp⟩

end YesMetaZFC.SetTheory.Internal
