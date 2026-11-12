import YesMetaZFC.Model.SetTheory.Demand.Untag
import YesMetaZFC.Model.SetTheory.Demand.Reply

/-! # 标签解码框架的完整一阶规格

七个内部对象由存在量词绑定；十个外部参数固定原树、标签树及两侧字母域。
完整初等性运输此公式时，目标自身的全部有限图、字母和逆像条件均被量化。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def td_retag_m {d} (ω A S U V e o T U' V' : Term d) : Formula 1 d := set[d] ⟪
  ∃ P Y F P' Y' F' f,
    ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(P,⌜U⌝ₛ,⌜V⌝ₛ) ∧
    ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(Y,⌜A⌝ₛ,P) ∧
    ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(P',⌜U'⌝ₛ,⌜V'⌝ₛ) ∧
    ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(Y',⌜A⌝ₛ,P') ∧
    ⌜(fseq_space_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,Y,F) ∧
    ⌜(fseq_space_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,Y',F') ∧
    ⌜tree_m⌝ₚ(F,⌜S⌝ₛ) ∧ ⌜(Formula.isBijectionFromTo kpair_convention_l)⌝ₚ(f,Y',Y) ∧
    (∀ x y, ⌜rd_entry0_m⌝ₚ(x,y,f) ↔ x ∈ Y' ∧ ⌜td_tag_m⌝ₚ(⌜e⌝ₛ,⌜o⌝ₛ,x,y)) ∧
    ⌜(tr_pull_m (𝒞 := kpair_convention_l))⌝ₚ(f,F',⌜S⌝ₛ,⌜T⌝ₛ) ∧
    (∀ z, z ∈ ⌜U'⌝ₛ ↔ ∃ a, a ∈ ⌜U⌝ₛ ∧ ⌜kpair0_m⌝ₚ(z,⌜e⌝ₛ,a)) ∧
    (∀ z, z ∈ ⌜V'⌝ₛ ↔ ∃ b, b ∈ ⌜V⌝ₛ ∧ ⌜kpair0_m⌝ₚ(z,⌜o⌝ₛ,b))⟫
derive_free_closed td_retag_m

theorem td_retag_sat_l {d} (ρ : Env M d) (ω A S U V e o T U' V' : Term d) :
    Formula.satisfies ρ (td_retag_m ω A S U V e o T U' V') ↔
      Nonempty (Td_retag_d hZF (ω.eval ρ) (A.eval ρ) (S.eval ρ) (U.eval ρ) (V.eval ρ)
        (e.eval ρ) (o.eval ρ) (T.eval ρ) (U'.eval ρ) (V'.eval ρ)) := by
  simp only [td_retag_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isCartesianProduct_iff I,fseq_space_sat_l I hZF.1,tree_sat_l,
    Formula.satisfies_isBijectionFromTo_iff I hZF.1,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,rd_entry0_sat_l hZF.1,Formula.satisfies_mem_iff,
    td_tag_sat_l hZF.1,tr_pull_sat_l I,kpair0_sat_l hZF.1,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨P,Y,F,P',Y',F',f,a,b,c,d,e,g,h,i,j,k,l,m⟩ => ⟨⟨P,Y,F,P',Y',F',f,a,b,c,d,e,g,h,i,j,k,l,m⟩⟩,
    fun ⟨r⟩ => ⟨r.P,r.Y,r.F,r.P',r.Y',r.F',r.f,r.pair,r.triple,r.pair',r.triple',r.space,r.space',
      r.source,r.map,r.decode,r.pull,r.left,r.right⟩⟩

end YesMetaZFC.SetTheory.Internal
