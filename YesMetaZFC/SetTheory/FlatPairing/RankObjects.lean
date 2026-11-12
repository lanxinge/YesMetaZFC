import YesMetaZFC.SetTheory.FlatPairing.Finite
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 后继秩层中的实际结构、赋值和编码轨道

平坦图的成员都留在前一层，所以完整 ω 赋值和完整编码轨道都只需要一个
后继层。有限前缀本身更低，仍在前一层；两种秩界在这里分别给出。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
local notation "J" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem fp_relation_rank_l {ω ν X R : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X)
    (hων : M.MemberSubset ω ν) (hR : M.IsSetRelationOn J R X) : M.MemberSubset R X := by
  intro p hp
  obtain ⟨x, y, code⟩ := hR.1 p hp
  obtain ⟨hx, hy⟩ := hR.2 x y ⟨p, code, hp⟩
  exact ((fp_fixed_l hZF.1 hω).mp code).rank_mem_l I hZF hω hV hων hx hy

theorem fp_function_rank_l {ω ν X A f : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X)
    (hων : M.MemberSubset ω ν) (hA : M.MemberSubset A X) (hf : M.IsSetFunctionFromTo J f A X) :
    M.MemberSubset f X := fp_relation_rank_l I hZF hω hV hων ⟨hf.1.1, fun _ _ h =>
      ⟨hA _ (hf.input_mem_of_pairMember h), hf.output_mem_of_pairMember h⟩⟩

/-- 每份实际赋值都自动得到平坦轨道，轨道的图是前一秩层的子集。 -/
theorem fp_trace_rank_l {ω ν X f : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X)
    (hων : M.MemberSubset ω ν) (hf : M.IsSetFunctionFromTo J f ω X) :
    ∃ H, Fs_trace_d J ω X f H ∧ M.MemberSubset H X := by
  have hωX : M.MemberSubset ω X := fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi)
  obtain ⟨H, hH⟩ := fs_trace_exists_l J hZF hω hf (fun z hz => by
    obtain ⟨e, he, heω⟩ := hω.1.1
    exact hωX z (hZF.1.eq_of_same_members e z (fun x => iff_of_false (he x) (hz x)) ▸ heω))
    (fun p x q hp hx code => ((fp_fixed_l hZF.1 hω).mp code).rank_mem_l I hZF hω hV hων hp hx)
  exact ⟨H, hH, fp_function_rank_l I hZF hω hV hων hωX hH.1⟩

theorem fp_finite_rank_l {ω ν X f n : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X)
    (hων : M.MemberSubset ω ν) (hf : M.IsSetFunctionFromTo J f ω X) (hn : M.mem n ω) :
    ∃ p, M.mem p X ∧ Fs_code_d J ω X f n p := by
  obtain ⟨H, hH, _⟩ := fp_trace_rank_l I hZF hω hV hων hf
  obtain ⟨p, hp, hnp⟩ := hH.1.2.2 n hn
  exact ⟨p, hp, H, hH, hnp⟩

/-- Vν 的隶属关系码和整个结构码均实际属于 V(ν+1)。 -/
theorem fp_model_rank_l {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν) :
    ∃ c R, M.mem c Y ∧ M.mem R Y ∧ Smem_d J c X R := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨c, R, hc, hr⟩ := smdl_membership_l J hZF ⟨z, ZF.v_ordinal_mem_l I hZF hV (hων z hzω)⟩
  have pow := ZF.v_successor_l I hZF hV hW hs
  have hR := (pow R).mpr (fp_relation_rank_l I hZF hω hV hων hc.2.2)
  have hX := (pow X).mpr (fun _ h => h)
  have hωμ : M.MemberSubset ω μ := fun x hx => (hs x).mpr (Or.inl (hων x hx))
  exact ⟨c, R, ((fp_fixed_l hZF.1 hω).mp hc.1).rank_mem_l I hZF hω hW hωμ hX hR, hR, hc, hr⟩

end YesMetaZFC.SetTheory
