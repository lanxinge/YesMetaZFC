import YesMetaZFC.SetTheory.LargeCardinal.Demand.AlphabetGround
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RetractionTree
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.Model.SetTheory.Demand.Reply

/-! # 收缩树变换的有限对象组

坐标依次为 ω、A、U、V、U×V、A×(U×V)、三个坐标的有限空间、
三元组有限空间、π、原树、逆像树、1、补全树。整个对象组有同一原公式，
可直接使用实际根腿的完整初等性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_frame_d (v : Fin 15 → M.Domain) : Prop where
  omega : M.IsOmega (v 0)
  pair : M.IsCartesianProduct I (v 4) (v 2) (v 3)
  triple : M.IsCartesianProduct I (v 5) (v 1) (v 4)
  inputs : Fseq_space_d I (v 0) (v 1) (v 6)
  left : Fseq_space_d I (v 0) (v 2) (v 7)
  right : Fseq_space_d I (v 0) (v 3) (v 8)
  space : Fseq_space_d I (v 0) (v 5) (v 9)
  source : Tree_d (v 9) (v 11)
  inverse : Tree_d (v 9) (v 12)
  alphabet : Td_alphabet_d (v 11) (v 2) (v 3)
  filled_alphabet : Td_alphabet_d (v 14) (v 2) (v 3)
  pull : Td_pull_d hZF (v 0) (v 1) (v 9) (v 10) (v 11) (v 12)
  fill : Tr_first_d hZF (v 9) (v 13) (v 12) (v 14)

def td_frame_m {d} (v : Fin 15 → Term d) : Formula 1 d :=
  .conj (Formula.isOmega (v 0)) (.conj (Formula.isCartesianProduct kpair_convention_l (v 4) (v 2) (v 3))
  (.conj (Formula.isCartesianProduct kpair_convention_l (v 5) (v 1) (v 4))
  (.conj (fseq_space_m (𝒞 := kpair_convention_l) (v 0) (v 1) (v 6))
  (.conj (fseq_space_m (𝒞 := kpair_convention_l) (v 0) (v 2) (v 7))
  (.conj (fseq_space_m (𝒞 := kpair_convention_l) (v 0) (v 3) (v 8))
  (.conj (fseq_space_m (𝒞 := kpair_convention_l) (v 0) (v 5) (v 9))
  (.conj (tree_m (v 9) (v 11)) (.conj (tree_m (v 9) (v 12))
  (.conj (td_alphabet_m (v 11) (v 2) (v 3)) (.conj (td_alphabet_m (v 14) (v 2) (v 3))
  (.conj (td_pull_bound_m (fun i => v (i.castAdd 2)))
    (tr_first_bound_m (v 0) (v 5) (v 9) (v 13) (v 12) (v 14)))))))))))))

@[simp] theorem td_frame_closed_l {d} (v : Fin 15 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (td_frame_m v).FreeClosed := by
  simp -implicitDefEqProofs [td_frame_m,Definitional.Formula.FreeClosed,hv]

theorem td_frame_sat_l {d} (ρ : Env M d) (v : Fin 15 → Term d) :
    Formula.satisfies ρ (td_frame_m v) ↔ Td_frame_d hZF (fun i => (v i).eval ρ) := by
  simp only [td_frame_m,Formula.satisfies_conj_iff,Formula.satisfies_isCartesianProduct_iff I,
    Formula.satisfies_isOmega_iff,fseq_space_sat_l I hZF.1,tree_sat_l,td_alphabet_sat_l hZF.1]
  constructor
  · rintro ⟨hw,pair,triple,inputs,left,right,space,source,inverse,alphabet,filled,pull,fill⟩
    exact ⟨hw,pair,triple,inputs,left,right,space,source,inverse,alphabet,filled,
      (td_pull_bound_sat_l hZF ρ _ inputs left right space source pair triple).mp pull,
      (tr_first_bound_sat_l hZF ρ _ _ _ _ _ _ space).mp fill⟩
  · intro frame
    exact ⟨frame.omega,frame.pair,frame.triple,frame.inputs,frame.left,frame.right,frame.space,frame.source,
      frame.inverse,frame.alphabet,frame.filled_alphabet,
      (td_pull_bound_sat_l hZF ρ _ frame.inputs frame.left frame.right frame.space frame.source frame.pair frame.triple).mpr frame.pull,
      (tr_first_bound_sat_l hZF ρ _ _ _ _ _ _ frame.space).mpr frame.fill⟩

theorem td_retraction_frame_l {ω A F₀ R π S U V z one a : M.Domain}
    (hw : M.IsOmega ω) (inputs : Fseq_space_d I ω A F₀) (retract : Tr_retract_d I ω A F₀ R π)
    (source : Td_tree_d I ω A S) (alphabet : Td_alphabet_d S U V) (chosen : M.mem a U)
    (separated : Td_separated_d S) (empty : ∀ x, ¬ M.mem x z) (succ : M.SuccessorOf one z) :
    ∃ P Y F₁ F₂ F T W, Td_frame_d hZF (fun i => [ω,A,U,V,P,Y,F₀,F₁,F₂,F,π,S,T,one,W].get i) ∧
      Td_tree_d I ω A W ∧ Td_separated_d W := by
  obtain ⟨P,Y,F,T,W,pair,triple,space,tree,pull,inverse,fill,_,target,letters,disjoint⟩ :=
    td_retraction_tree_l hZF hw inputs retract source alphabet chosen separated empty succ
  obtain ⟨F₁,left⟩ := ZF.fseq_space_exists_l I hZF hw U
  obtain ⟨F₂,right⟩ := ZF.fseq_space_exists_l I hZF hw V
  exact ⟨P,Y,F₁,F₂,F,T,W,⟨hw,pair,triple,inputs,left,right,space,tree,inverse,alphabet,letters,pull,fill⟩,target,disjoint⟩

end YesMetaZFC.SetTheory.LargeCardinal
