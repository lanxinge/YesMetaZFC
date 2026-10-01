import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.WellOrder

/-! # 序数参数界给出的统一集合界

语法证书中的叶参数及有限标签都被同一序数界住。其 rudimentary 闭包包含
整份证书的所有构造码；这一步不使用 J 求值或 V=L。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem ps_cert_hull_l (hM : M.Models KPi) {F T a C n c : M.Domain} (hf : Ps_cert_d F T)
    (ha : ∀ b, M.mem b T → M.IsOrdinal b → M.mem b a) (hC : Rd_closure_d a C)
    (hc : Rd_entry_d n c F) : M.mem c C := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  obtain ⟨closed, inc, _⟩ := rd_closure_spec_l hM hC
  let ρ := ((jh_env_l F).push F).push C
  let φ : UnarySchema 2 := { body := .forallE (.imp (rd_entry0_m (.bound 1) .newest (.bound 3)) (.mem .newest (.bound 2))) }
  have hφ h : φ.denote ρ h ↔ ∀ c, Rd_entry_d h c F → M.mem c C := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_mem_iff]; rfl
  apply (hφ n).mp (hi φ ρ ?_ n) c hc
  intro h ih
  apply (hφ h).mpr
  intro c hc
  have child {d} (hd : Ps_read_d F h d) : M.mem d C := hd.elim fun m hm => (hφ m).mp (ih m hm.1) d hm.2
  have tag {k t} (ht : M.mem t T) (hn : Internal.Num_d k t) : M.mem t C :=
    inc t (ha t ht (KPi.n0_ordinal_l hM (po_num_natural_l hKP.1 hn)))
  rcases (hf.at_l hc).2.2.2 with ⟨b, hb, ⟨t, ht, hn, hp⟩, ho⟩ |
    ⟨k, x, _, y, _, z, _, ⟨t, ht, p, _, hn, hp, he⟩, hx, hy, hz⟩
  · exact closed .opair t b t (tag ht hn) (inc b (ha b hb ho)) (tag ht hn) c (rd_opair_value_l hKP.1 hp)
  · have hpC := closed .triple x y z (child hx) (child hy) (child hz) p (rd_triple_value_l hKP.1 hp)
    exact closed .opair t p t (tag ht hn) hpC (tag ht hn) c (rd_opair_value_l hKP.1 he)

theorem po_code_bound_l (hM : M.Models KPi) {c : M.Domain} (hc : Ps_valid_d c) :
    ∃ a C, M.IsOrdinal a ∧ Rd_closure_d a C ∧ M.mem c C := by
  obtain ⟨n, T, F, hf, hc⟩ := hc
  obtain ⟨B, hB⟩ := KP.exists_pair (KPi.models_iff_l.mp hM).1 T T
  obtain ⟨a, ha, hb⟩ := KPi.ordinal_bound_l hM B
  obtain ⟨C, hC⟩ := rd_closure_exists_l hM a
  exact ⟨a, C, ha, hC, ps_cert_hull_l hM hf (hb T ((hB T).mpr (Or.inl rfl))) hC hc⟩

end YesMetaZFC.SetTheory.InnerModel
