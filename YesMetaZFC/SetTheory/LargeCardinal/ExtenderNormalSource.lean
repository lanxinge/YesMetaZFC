import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctionCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderShort
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Bounded

/-! # 正规性在子集一致的源之间传递

正规性只测试施加源中的 κ 值代表。有限列图编码证明这些代表属于原来
的所属模型，因此跨模型施加保留实际正规性，而不额外假设正规性操作。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def En_source_d (ω κ L X F : M.Domain) : Prop := ∀ n a U D f i α A,
  M.mem n ω → Fn0_d n L a → Rd_entry_d a U F → Ep_space_d κ n D →
  M.mem f X → Fn0_d D κ f → Rd_entry_d i α a → M.mem A U →
  (∀ s, M.mem s A → ∀ x y, Rd_entry_d s x f → Rd_entry_d i y s → M.mem x y) →
  ∃ m b V β B, M.mem m ω ∧ M.SuccessorOf m n ∧ Fn0_d m L b ∧ M.MemberSubset a b ∧
    Rd_entry_d n β b ∧ M.mem β α ∧ Rd_entry_d b V F ∧ M.mem B V ∧
    ∀ s, M.mem s B → En_graph_d n κ A f s

theorem En_normal_d.source_l {ω κ L F : M.Domain} (h : En_normal_d ω κ L F) (X : M.Domain) :
    En_source_d ω κ L X F := fun n a U D f i α A hn ha hu hd _ => h n a U D f i α A hn ha hu hd

theorem En_source_d.transfer_l (hZF : M.Models ZF) {ω κ K N R K' X S L F : M.Domain}
    (h : En_source_d ω κ L N F) (owner : Ep_source_d hZF ω κ K N R)
    (source : Ep_source_d hZF ω κ K' X S) (subsets : Ea_subset_d ω κ X N) : En_source_d ω κ L X F := by
  intro n a U D f i α A hn ha hu hd hf hfn
  exact h n a U D f i α A hn ha hu hd
    (subsets.function_l hZF source owner hn hd hf hfn) hfn

end YesMetaZFC.SetTheory.LargeCardinal
