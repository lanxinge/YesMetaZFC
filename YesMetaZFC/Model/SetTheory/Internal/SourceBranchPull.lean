import YesMetaZFC.Model.SetTheory.Internal.SourceBranchSyntax
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingCountable
import YesMetaZFC.SetTheory.CumulativeRelativeClosure

/-! # 枝反射沿完整初等图回拉

先把外部下降链映入目标，由目标反射取得内部分支，再反射一个 Δ₀ 存在句。
此方向不需要共同纤维，也不需要额外选择公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem Sc_branch_d.pull_l {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hωX : M.mem ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (branches : Sc_branch_d ω Y) : Sc_branch_d ω X := by
  intro A P hA hP ⟨f, hf, hd⟩
  obtain ⟨B, hB, hAB⟩ := hj.1.1.2.2 A hA
  obtain ⟨Q, hQ, hPQ⟩ := hj.1.1.2.2 P hP
  have ff := fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l (hX A hA))
  obtain ⟨g, hg, comp⟩ := ZF.exists_compositionFunction hZF I ff hj.1.1
  have gf : Fn0_d ω B g := (fn0_of_function_l (ZF.modelsKP hZF) hg).retarget_l (fun i y hiy => by
    obtain ⟨_, x, hix, hxy⟩ := (comp i y).mp hiy
    exact ((hn.2 y B).mp ((hj.relation_l I hZF hω hm.1 hn.1 hxy hAB).mp
      ((hm.2 x A).mpr ⟨hj.1.1.input_mem_of_pairMember hxy, hA, (hf.bound_l hix).2⟩))).2.2)
  have gd : Wf_desc_d Q g := by
    intro i m x y hmi hix hmy
    obtain ⟨_, a, hia, hax⟩ := (comp i x).mp hix
    obtain ⟨_, b, hmb, hby⟩ := (comp m y).mp hmy
    exact (hj.entry_l hZF hω hX hY hm hn hby hax hPQ).mp (hd i m a b hmi hia hmb)
  obtain ⟨g', hg', gg⟩ := branches B Q hB hQ ⟨g, gf, gd⟩
  have tr := hj.exists_delta_l hZF hω hX hY hm hn (n := 3)
    (sb_chain_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (sb_chain_delta_l ..)
    ⟨Fin.cases P (Fin.cases A (fun _ => ω)), fun _ => A⟩
    ⟨Fin.cases Q (Fin.cases B (fun _ => ω)), fun _ => B⟩
    (Fin.cases hPQ (Fin.cases hAB (fun _ => hj.omega_l I hZF hω hX hY hm hn hωX)))
  obtain ⟨f', hf', hs⟩ := tr.mpr ⟨g', hg', (sb_chain_sat_l hZF.1 ..).mpr gg⟩
  exact ⟨f', hf', (sb_chain_sat_l hZF.1 ..).mp hs⟩

/-- 极限相对秩段中的枝只增加有限层秩；此处不要求正则性。 -/
theorem Sc_branch_d.rank_l {ω Z α V : M.Domain} (branches : Sc_branch_d ω Z)
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hωV : M.mem ω V) : Sc_branch_d ω V := by
  intro A R hA hR branch
  obtain ⟨f, hf, fn, desc⟩ := branches A R (hZ V hV A hA) (hZ V hV R hR) branch
  exact ⟨f, rank.relation_mem_l hZF hZ hV hα hωV hA hf (fun p hp => fn.1 p hp), fn, desc⟩

end YesMetaZFC.SetTheory.Internal
