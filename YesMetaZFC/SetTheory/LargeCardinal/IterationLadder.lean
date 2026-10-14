import YesMetaZFC.SetTheory.LargeCardinal.IterationWellFounded
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.AscendingDescent

/-! # 可沿可数壳搬运的分支下降见证

每项是原结点与原元素的有序对；后项属于前项在同一真实树边下的像。
全部见证有一个传递集合界，因而证书为 Δ₀，不涉及壳的外部可数闭性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_ladder_d (ω B Q G H D f : M.Domain) : Prop := Fn0_d ω D f ∧
  (∀ u, M.mem u D → ∃ i, M.mem i B ∧ ∃ x, M.mem x H ∧ ∃ c, M.mem c H ∧
    ∃ X, M.mem X H ∧ ∃ R, M.mem R H ∧ KPair_d M u i x ∧ Rd_entry_d i c Q ∧ KPair_d M c X R ∧ M.mem x X) ∧
  ∀ n m u v, M.mem n ω → M.mem m ω → M.mem u D → M.mem v D →
    M.SuccessorOf m n → Rd_entry_d n u f → Rd_entry_d m v f →
    ∃ i, M.mem i H ∧ ∃ j, M.mem j H ∧ ∃ x, M.mem x H ∧ ∃ y, M.mem y H ∧
    ∃ a, M.mem a H ∧ ∃ g, M.mem g H ∧ ∃ z, M.mem z H ∧
      KPair_d M u i x ∧ KPair_d M v j y ∧ KPair_d M a i j ∧ Rd_entry_d a g G ∧ Rd_entry_d x z g ∧ M.mem y z

def it_ladder_m {d} (ω B Q G H D f : Term d) : Formula 1 d := set[d] ⟪⌜fn0_m⌝ₚ(⌜ω⌝ₛ, ⌜D⌝ₛ, ⌜f⌝ₛ) ∧
  (∀ u ∈ ⌜D⌝ₛ, ∃ i ∈ ⌜B⌝ₛ, ∃ x ∈ ⌜H⌝ₛ, ∃ c ∈ ⌜H⌝ₛ, ∃ X ∈ ⌜H⌝ₛ, ∃ R ∈ ⌜H⌝ₛ,
    ⌜kpair0_m⌝ₚ(u, i, x) ∧ ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(c, X, R) ∧ x ∈ X) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∀ m ∈ ⌜ω⌝ₛ, ∀ u ∈ ⌜D⌝ₛ, ∀ v ∈ ⌜D⌝ₛ,
    ⌜KP.succ0_m⌝ₚ(m, n) → ⌜rd_entry0_m⌝ₚ(n, u, ⌜f⌝ₛ) → ⌜rd_entry0_m⌝ₚ(m, v, ⌜f⌝ₛ) →
    ∃ i ∈ ⌜H⌝ₛ, ∃ j ∈ ⌜H⌝ₛ, ∃ x ∈ ⌜H⌝ₛ, ∃ y ∈ ⌜H⌝ₛ, ∃ a ∈ ⌜H⌝ₛ, ∃ g ∈ ⌜H⌝ₛ, ∃ z ∈ ⌜H⌝ₛ,
      ⌜kpair0_m⌝ₚ(u, i, x) ∧ ⌜kpair0_m⌝ₚ(v, j, y) ∧ ⌜kpair0_m⌝ₚ(a, i, j) ∧
      ⌜rd_entry0_m⌝ₚ(a, g, ⌜G⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, z, g) ∧ y ∈ z)⟫
derive_free_closed it_ladder_m

theorem it_ladder_delta_l {d} (ω B Q G H D f : Term d) : (it_ladder_m ω B Q G H D f).IsDelta0 :=
by
  unfold it_ladder_m
  repeat first
    | exact fn0_delta_l .. | exact kpair0_delta_l .. | exact rd_entry0_delta_l .. | exact KP.succ0_delta_l .. | exact .mem ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem
    | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.imp

theorem it_ladder_sat_l (hKP : M.Models KP) {d} (η : Env M d) (ω B Q G H D f : Term d) :
    Formula.satisfies η (it_ladder_m ω B Q G H D f) ↔
      It_ladder_d (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (H.eval η) (D.eval η) (f.eval η) := by
  simp only [it_ladder_m, It_ladder_d, Formula.satisfies_conj_iff, fn0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    KP.succ0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f, nodes, steps⟩ => ⟨f, nodes, fun n m u v hn hm hu hv => steps n hn m hm u hu v hv⟩,
    fun ⟨f, nodes, steps⟩ => ⟨f, nodes, fun n hn m hm u hu v hv => steps n m u v hn hm hu hv⟩⟩

theorem It_ill_branch_d.ladder_l (hZF : M.Models ZF) {ω α T Q G B : M.Domain}
    (dc : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (members : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (bad : It_ill_branch_d hZF ω α T Q G B) : ∃ H D f, It_ladder_d ω B Q G H D f := by
  classical
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, L, D, p, A, R, q, c, N, V, _, system, _, limit, _, ill⟩ := bad
  have descent : ∃ f, Fn0_d ω D f ∧ ∀ n m u v, M.SuccessorOf m n →
      Rd_entry_d n u f → Rd_entry_d m v f → Di_step_d p A R u v := by
    apply Classical.byContradiction
    intro no
    exact ill (di_wf_of_no_step_l hZF dc system.system limit
      (fun f hf hs => no ⟨f, hf, hs⟩))
  obtain ⟨f, ff, steps⟩ := descent
  obtain ⟨U, us⟩ := KP.exists_pair (ZF.modelsKP hZF) Q G
  obtain ⟨W, ws⟩ := KP.exists_pair (ZF.modelsKP hZF) U D
  obtain ⟨H, trans, hWH, _⟩ := ZF.tc_exists_l I hZF W
  have hUH := trans W hWH U ((ws U).mpr (Or.inl rfl))
  have hD := trans W hWH D ((ws D).mpr (Or.inr rfl))
  have hQ := trans U hUH Q ((us Q).mpr (Or.inl rfl))
  have hG := trans U hUH G ((us G).mpr (Or.inr rfl))
  refine ⟨H, D, f, ff, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, x, hi, pair, c, X, R, hc, code, hx⟩ := (system.tags.nodes u).mp hu
    have hcode := (rd_entry_transitive_l trans hQ hc).2
    have own := code.mem_l M trans hcode
    exact ⟨i, hi, x, trans X own.1 x hx, c, hcode, X, own.1, R, own.2, pair, hc, code, hx⟩
  · intro n m u v _ _ hu hv succ hnu hmv
    obtain ⟨j, w, hvj, hwj, huw, hvw⟩ := steps n m u v succ hnu hmv
    obtain ⟨i, x, _, ux, _⟩ := (system.tags.nodes u).mp hu
    obtain ⟨y, vy, _⟩ := system.tags.label_l hvj
    obtain ⟨z, wz, _⟩ := system.tags.label_l hwj
    obtain ⟨_, _, g, hg, hxz⟩ := (system.arrows u w i j x z ux wz).mp huw
    obtain ⟨_, _, c, X, S, hc, code, hyz⟩ := (system.tags.relation_l vy wz).mp hvw
    obtain ⟨X₀, S₀, mx⟩ := members j c hc
    obtain ⟨eqX, eqS⟩ := kpair_injective_l M code mx.1.1
    subst X₀ S₀
    obtain ⟨a, pair, ha⟩ := hg
    have ag := rd_entry_transitive_l trans hG ha
    have ij := pair.mem_l M trans ag.1
    have xz := rd_entry_transitive_l trans ag.2 hxz
    have yH := (vy.mem_l M trans (trans D hD v hv)).2
    exact ⟨i, ij.1, j, ij.2, x, xz.1, y, yH, a, ag.1, g, ag.2, z, xz.2,
      ux, vy, pair, ha, hxz, ((mx.2 y z).mp hyz).2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal
