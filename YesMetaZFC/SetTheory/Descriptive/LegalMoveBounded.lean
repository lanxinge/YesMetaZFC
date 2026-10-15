import YesMetaZFC.SetTheory.Descriptive.LeastLegalMove

/-! # 合法追加的有界读法

在既定有限历史空间中，追加关系只量化旧 L、ω 和实际图的成员。
这个等价式用于成员满地嵌入，避免把含类型语义的游戏规则重新解释于扩张。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ds_end_bound_m {d} (ω X t h a : Term d) : Formula 1 d := set[d] ⟪∃ n ∈ ⌜ω⌝ₛ, ∃ m ∈ ⌜ω⌝ₛ,
  ⌜fn0_m⌝ₚ(n, ⌜X⌝ₛ, ⌜h⌝ₛ) ∧ ⌜fn0_m⌝ₚ(m, ⌜X⌝ₛ, ⌜t⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(m, n) ∧
  ⌜h⌝ₛ ⊆ ⌜t⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(n, ⌜a⌝ₛ, ⌜t⌝ₛ)⟫
derive_free_closed ds_end_bound_m

theorem ds_end_bound_delta_l {d} (ω X t h a : Term d) : (ds_end_bound_m ω X t h a).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..)
    (.conj (KP.succ0_delta_l ..) (.conj (.atom _ (by decide) _) (rd_entry0_delta_l ..))))))

theorem ds_end_bound_sat_l {d} (ρ : Env M d) (ω X t h a : Term d)
    (hw : M.IsOmega (ω.eval ρ)) {F : M.Domain} (space : Fseq_space_d I (ω.eval ρ) (X.eval ρ) F)
    (ht : M.mem (t.eval ρ) F) (hh : M.mem (h.eval ρ) F) :
    Formula.satisfies ρ (ds_end_bound_m ω X t h a) ↔ Fseq_end_d I (ω.eval ρ) (t.eval ρ) (h.eval ρ) (a.eval ρ) := by
  simp only [ds_end_bound_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hZF.1, KP.succ0_sat_l hZF.1, Formula.satisfies_subset_iff, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨n, hn, m, hm, fh, ft, succ, sub, last⟩
    have fh := fn0_function_l (ZF.modelsKP hZF) fh
    have ft := fn0_function_l (ZF.modelsKP hZF) ft
    exact ⟨m, n, ⟨hm, hw.members_areOrdinals hZF m hm, ft.1, ft.2.1⟩, hn, succ,
      ⟨hn, hw.members_areOrdinals hZF n hn, fh.1, fh.2.1⟩, (ds_restrict_iff_l I fh ft.1).mpr sub, last⟩
  · rintro ⟨m, n, decomp⟩
    obtain ⟨j, hj, fh⟩ := (space (h.eval ρ)).mp hh
    obtain ⟨k, hk, ft⟩ := (space (t.eval ρ)).mp ht
    have ej := fh.2.1.eq hZF.1 decomp.prefix_sequence.2.2.2
    have ek := ft.2.1.eq hZF.1 decomp.source.2.2.2
    subst j k
    exact ⟨n, hj, m, hk, fn0_of_function_l (ZF.modelsKP hZF) fh, fn0_of_function_l (ZF.modelsKP hZF) ft,
      decomp.length_successor, Fseq_end_d.subset_l I ⟨m, n, decomp⟩, decomp.last_value⟩

def cg_admit_bound_m {d} (ω X L h a : Term d) : Formula 1 d :=
  .existsMem L (ds_end_bound_m ω.weaken X.weaken .newest h.weaken a.weaken)
derive_free_closed cg_admit_bound_m

theorem cg_admit_bound_delta_l {d} (ω X L h a : Term d) : (cg_admit_bound_m ω X L h a).IsDelta0 :=
  .existsMem _ (ds_end_bound_delta_l ..)

theorem cg_admit_bound_sat_l {d} (ρ : Env M d) (ω X L h a : Term d)
    (hw : M.IsOmega (ω.eval ρ)) {F : M.Domain} (space : Fseq_space_d I (ω.eval ρ) (X.eval ρ) F)
    (legal : M.MemberSubset (L.eval ρ) F) (hh : M.mem (h.eval ρ) F) :
    Formula.satisfies ρ (cg_admit_bound_m ω X L h a) ↔ Cg_admit_d hZF (ω.eval ρ) (L.eval ρ) (h.eval ρ) (a.eval ρ) := by
  simp only [cg_admit_bound_m, Formula.satisfies_existsMem_iff, Cg_admit_d]
  refine exists_congr fun t => and_congr_right fun ht => ?_
  simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
    ds_end_bound_sat_l hZF (ρ.push t) ω.weaken X.weaken .newest h.weaken a.weaken
      (by simpa only [Definitional.Term.eval_weaken] using hw)
      (by simpa only [Definitional.Term.eval_weaken] using space) (legal t ht)
      (by simpa only [Definitional.Term.eval_weaken] using hh)

end YesMetaZFC.SetTheory.Descriptive
