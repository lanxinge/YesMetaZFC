import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalResult
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyPadding
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 原树与复制历史的同步恒等延伸

实际空操作延长原树，同一末行随后进入复制历史。原支撑列保持不变，
共同端点的界随原模型列换读，再沿恒等边保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 复制已经选定的填充边；原图及恒等后继均不重新选择。 -/
theorem Ic_history_d.copy_pad_l
    {ω c n m T Q G E L H S Qw Gw θ T₁ Q₁ G₁ E₁ : M.Domain}
    (tree : It_tree_d hZF ω c m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E L m H S Qw Gw) (hm : M.SuccessorOf m n)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (next : It_tree_d hZF ω c θ T₁ Q₁ G₁ E₁)
    (extension : It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁)
    (empty : ∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p) :
    ∃ H₁ S₁ Qw₁ Gw₁,
      (∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      Ic_history_d hZF ω T₁ Q₁ G₁ E₁ L θ H₁ S₁ Qw₁ Gw₁ ∧
      M.MemberSubset H H₁ ∧ M.MemberSubset Qw Qw₁ ∧ M.MemberSubset Gw Gw₁ ∧
      ∀ N R B σ u U β χ, Ic_at_d H n N B σ u U β → Ic_bound_d I H Q N R σ n χ →
        Ic_at_d H₁ m N B σ u U β ∧ Ic_bound_d I H₁ Q₁ N R σ m χ := by
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have inactive ρ (hρ : Rd_entry_d n ρ L) : False := by
    obtain ⟨p,κ,F,hp,_⟩ := (levels n ρ).mp hρ
    obtain ⟨k,hk,sk⟩ := (tree.move_domain n).mp ⟨p,hp⟩
    exact ir m (sk.eq hZF.1 hm ▸ hk)
  have lv := extension.levels_pad_l empty levels
  have order i j (hj : M.mem j m) : Rd_entry_d i j T₁ ↔ Rd_entry_d i j T :=
    (extension.2.1 i j).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hj)).elim),Or.inl⟩
  have prior := hist.original_prefix_l hZF hm order
    (fun i a _ => extension.2.2.1 i a)
    (fun i j f hj => (extension.2.2.2.1 i j f hj).mp)
    (fun i p hi => (extension.2.2.2.2.2 i p (fun eq => ir n (eq ▸ hi))).mp)
    (fun _ _ _ => Iff.rfl)
  obtain ⟨l,H₁,S₁,Qw₁,Gw₁,sl,history,hh,hq,hg,rows⟩ :=
    prior.pad_extend_l hZF next lv hm extension.1.predecessor_mem inactive
  have eq := sl.eq hZF.1 extension.1
  subst l
  exact ⟨H₁,S₁,Qw₁,Gw₁,lv,history,hh,hq,hg,fun N R B σ u U β χ row bound =>
    rows N R B σ u U β χ row (hist.bound_extend_l hZF tree next extension hm.predecessor_mem bound)⟩

theorem Ic_history_d.original_pad_l
    {ω c n m T Q G E L H S Qw Gw : M.Domain}
    (tree : It_tree_d hZF ω c m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E L m H S Qw Gw) (hm : M.SuccessorOf m n)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F) :
    ∃ θ T₁ Q₁ G₁ E₁ d j H₁ S₁ Qw₁ Gw₁,
      M.SuccessorOf θ m ∧ It_tree_d hZF ω c θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d n d Q ∧ Rd_entry_d m d Q₁ ∧ It_map_d G₁ n m j ∧
      (∀ x y, Rd_entry_d x y j → x = y) ∧
      (∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p) ∧
      (∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      Ic_history_d hZF ω T₁ Q₁ G₁ E₁ L θ H₁ S₁ Qw₁ Gw₁ ∧
      M.MemberSubset H H₁ ∧ M.MemberSubset Qw Qw₁ ∧ M.MemberSubset Gw Gw₁ ∧
      ∀ N R B σ u U β χ, Ic_at_d H n N B σ u U β → Ic_bound_d I H Q N R σ n χ →
        Ic_at_d H₁ m N B σ u U β ∧ Ic_bound_d I H₁ Q₁ N R σ m χ := by
  obtain ⟨θ,T₁,Q₁,G₁,E₁,d,j,succ,next,extension,old,node,edge,identity,keep,empty⟩ :=
    it_pad_l hZF tree hm
  obtain ⟨H₁,S₁,Qw₁,Gw₁,lv,history,hh,hq,hg,rows⟩ :=
    hist.copy_pad_l hZF tree hm levels next extension empty
  exact ⟨θ,T₁,Q₁,G₁,E₁,d,j,H₁,S₁,Qw₁,Gw₁,succ,next,extension,old,node,edge,identity,
    empty,lv,history,hh,hq,hg,rows⟩

end YesMetaZFC.SetTheory.LargeCardinal
