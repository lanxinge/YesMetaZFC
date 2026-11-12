import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail

/-! # 原关系中的有限空间与树沿实际图进入传递目标

自然数像由调用处的完整数字图给出。读取整个有限空间只用目标的配对与并集闭性，
树的前缀封闭性则是有界真值；原模型无需隶属呈示，也不要求整个目标满足ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.tree_space_l {ω c X R d N W j w A F S A' F' S' : M.Domain}
    (hw : M.IsOmega ω) (source : Smdl_d I c X R) (target : Smem_d I d N W)
    (nt : M.TransitiveSet N) (map : Smap_d I ω c d X N j)
    (pair : ∀ a b, M.mem a N → M.mem b N → ∃ p, M.mem p N ∧ Pair_d M p a b)
    (union : ∀ a, M.mem a N → ∃ p, M.mem p N ∧ M.IsUnionOf p a)
    (iw : Rd_entry_d w ω j) (ia : Rd_entry_d A A' j)
    (iF : Rd_entry_d F F' j) (iS : Rd_entry_d S S' j)
    (space : Sc_fseq_d I w A F X R)
    (closed : Rr_truth_d I X R (tree_m (.bound 1) .newest) (Fin.cases S (fun _ : Fin 1 => F))) :
    Fseq_space_d I ω A' F' ∧ Tree_d F' S' := by
  have moved : Sc_fseq_d I ω A' F' N W := space.map_l I hZF hw source target.1 map
    (by simp -implicitDefEqProofs) (Fin.cases iF (Fin.cases ia (fun _ => iw)))
  have finite := (sc_fseq_mem_l I (ZF.modelsKP hZF) hw nt target
    (map.1.1.output_mem_of_pairMember iw) (map.1.1.output_mem_of_pairMember ia)
    (map.1.1.output_mem_of_pairMember iF) pair union).mp moved
  have tree : Rr_truth_d I N W (tree_m (.bound 1) .newest)
      (Fin.cases S' (fun _ : Fin 1 => F')) := closed.map_l I hZF hw source target.1 map
    (by simp -implicitDefEqProofs) (Fin.cases iS (fun _ => iF))
  let ρ : Env M 2 := ⟨Fin.cases S' (fun _ => F'),fun _ => S'⟩
  exact ⟨finite,(tree_sat_l ρ (.bound 1) .newest).mp
    ((rr_truth_mem_l I nt target (tree_m (.bound 1) .newest)
      (.conj (.atom ..) (.forallMem _ (.forallMem _ (.imp (.atom ..) (.mem ..)))))
      (Fin.cases S' (fun _ : Fin 1 => F'))).mp tree).2⟩

end YesMetaZFC.SetTheory.LargeCardinal
