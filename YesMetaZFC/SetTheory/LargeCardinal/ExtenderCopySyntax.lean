import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyComponent
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 双映射复制的带支撑代表方程 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_node_d (π σ q u E : M.Domain) : Prop := ∃ a B a' D v, KPair_d M u a B ∧ Rd_entry_d a a' σ ∧
  Ec_class_d π B D ∧ KPair_d M v a' D ∧ Rd_entry_d v E q

def ec_node_m {d} (π σ q u E : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj (kpair_m (w u) (.bound 4) (.bound 3))
    (.conj (rd_entry_m (.bound 4) (.bound 2) (w σ)) (.conj (ec_class_m (w π) (.bound 3) (.bound 1))
      (.conj (kpair_m .newest (.bound 2) (.bound 1)) (rd_entry_m .newest (w E) (w q))))))))))
derive_free_closed ec_node_m

theorem ec_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (π σ q u E : Term d) :
    Formula.satisfies ρ (ec_node_m π σ q u E) ↔
      Ec_node_d (π.eval ρ) (σ.eval ρ) (q.eval ρ) (u.eval ρ) (E.eval ρ) := by
  simp only [ec_node_m, Ec_node_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, ec_class_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 同一对极限上的完整复制证书，包括实际常值方块、唯一性与良基性回传。 -/
def Ec_limit_d (hZF : M.Models ZF) (ω c X d Y π σ q q' e C W e' C' W' : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ τ i i', Smap_d I ω e e' C C' τ ∧
      Smap_d I ω c e X C i ∧ Smap_d I ω d e' Y C' i' ∧
      (∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧ Ec_node_d π σ q' u E) ∧
      (∀ x x' B E, Rd_entry_d x x' π → Rd_entry_d x B i → (Rd_entry_d B E τ ↔ Rd_entry_d x' E i')) ∧
      (∀ k, Fn0_d C C' k → (∀ u B E, Rd_entry_d u B q → Ec_node_d π σ q' u E → Rd_entry_d B E k) → k = τ) ∧
      (Wf_rel_d C' W' → Wf_rel_d C W)
end YesMetaZFC.SetTheory.LargeCardinal
