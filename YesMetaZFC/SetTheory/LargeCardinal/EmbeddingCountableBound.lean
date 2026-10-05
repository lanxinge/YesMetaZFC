import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource
import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaBound

/-! # 模型内可数嵌入的序数限制具有实际小界

源内的单射图把 σ 的条目编号到 ω。统一化收集编号条目的第二坐标，
模型内不可数共尾性给出严格界；序数不下降性同时界住第一坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ec_count_value_m {n} (σ ι κ i y : Term n) : Formula 1 n :=
  Formula.existsMem σ (Formula.existsMem κ.weaken
    (.conj (kpair0_m (.bound 1) .newest y.weaken.weaken)
      (rd_entry0_m (.bound 1) i.weaken.weaken ι.weaken.weaken)))
derive_free_closed ec_count_value_m

theorem ec_count_value_delta_l {n} (σ ι κ i y : Term n) : (ec_count_value_m σ ι κ i y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..)))

theorem ec_count_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (σ ι κ i y : Term n) :
    Formula.satisfies ρ (ec_count_value_m σ ι κ i y) ↔ ∃ p, M.mem p (σ.eval ρ) ∧
      ∃ a, M.mem a (κ.eval ρ) ∧ KPair_d M p a (y.eval ρ) ∧ Rd_entry_d p (i.eval ρ) (ι.eval ρ) := by
  simp only [ec_count_value_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem smap_countable_bound_l (hZF : M.Models ZF) {ω φ K Z S U R c d σ ι κ : M.Domain}
    (owner : Ep_source_d hZF ω φ K Z S) (hU : M.TransitiveSet U)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c U R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Z S)
    (hσ : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d U Z σ)
    (hσZ : M.mem σ Z) (hιZ : M.mem ι Z)
    (countable : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) ι σ ω)
    (hκ : M.IsOrdinal κ) (hκφ : Rd_entry_d κ φ σ) (regular : Sc_omega_bound_d ω Z φ) :
    ∃ μ, M.mem μ φ ∧ ∀ a b, M.mem a κ → Rd_entry_d a b σ → M.mem a μ ∧ M.mem b μ := by
  classical
  let I := kp_pair_l (ZF.modelsKP hZF)
  have κU := hσ.1.1.input_mem_of_pairMember hκφ
  have κZ := (rd_entry_transitive_l owner.transitive hσZ hκφ).1
  have φord := hσ.ordinal_l hZF owner.omega hU owner.transitive hm hn hκφ hκ
  have into a b (ha : M.mem a κ) (hab : Rd_entry_d a b σ) : M.mem b φ :=
    ((hn.2 b φ).mp ((hσ.relation_l I hZF owner.omega hm.1 hn.1 hab hκφ).mp
      ((hm.2 a κ).mpr ⟨hU κ κU a ha, κU, ha⟩))).2.2
  let P i y := ∃ p, M.mem p σ ∧ ∃ a, M.mem a κ ∧ KPair_d M p a y ∧ Rd_entry_d p i ι
  have unique i x y (hx : P i x) (hy : P i y) : x = y := by
    obtain ⟨p, _, a, _, hp, hpi⟩ := hx
    obtain ⟨q, _, b, _, hq, hqi⟩ := hy
    have eq := countable.2 p q i hpi hqi
    exact (kpair_injective_l M (eq ▸ hp) hq).2
  have value_bound i y (hy : P i y) : M.mem y φ := by
    obtain ⟨p, hp, a, ha, hpa, _⟩ := hy
    exact into a y ha ⟨p, hpa, hp⟩
  obtain ⟨z, _, hzω⟩ := owner.omega.1.1
  have hzφ := owner.below z hzω
  let ρ : Env M 5 := ⟨Fin.cases σ (Fin.cases ι (Fin.cases κ (Fin.cases φ (fun _ => z)))), fun _ => z⟩
  let ψ : BinarySchema 5 := {
    body := .disj (ec_count_value_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest)
      (.conj (.neg (Formula.existsMem (.bound 5)
        (ec_count_value_m (.bound 3) (.bound 4) (.bound 5) (.bound 2) .newest)))
        (Formula.extensionalEq .newest (.bound 6))) }
  have sat i y : ψ.denote ρ i y ↔ P i y ∨ (¬ (∃ v, M.mem v φ ∧ P i v) ∧ y = z) := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_disj_iff, ec_count_value_sat_l hZF.1,
      Formula.satisfies_conj_iff, Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨f, C, hfZ, _, hf, select⟩ := sc_uniform_source_l hZF owner.omega owner.transitive hn owner.theory ψ
    (.disj (ec_count_value_delta_l ..) (.conj (.neg (.existsMem _ (ec_count_value_delta_l ..))) (.atom _ _ _)))
    ρ (Fin.cases hσZ (Fin.cases hιZ (Fin.cases κZ (Fin.cases owner.cardinal_mem
      (fun _ => owner.transitive ω owner.omega_mem z hzω))))) owner.omega_mem (fun i _ => by
        by_cases hi : ∃ y, M.mem y φ ∧ P i y
        · obtain ⟨y, hy, hiy⟩ := hi
          exact ⟨y, owner.transitive φ owner.cardinal_mem y hy, (sat i y).mpr (Or.inl hiy)⟩
        · exact ⟨z, owner.transitive ω owner.omega_mem z hzω, (sat i z).mpr (Or.inr ⟨hi, rfl⟩)⟩)
  have ff := hf.retarget_l (fun i y hiy => ((sat i y).mp (select i y hiy)).elim
    (value_bound i y) (fun h => h.2.symm ▸ hzφ))
  obtain ⟨μ, hμ, bound⟩ := regular f hfZ ff
  refine ⟨μ, hμ, fun a b ha hab => ?_⟩
  obtain ⟨p, hp, hpσ⟩ := hab
  obtain ⟨i, hi, hpi⟩ := countable.1.2.2 p hpσ
  have hib : P i b := ⟨p, hpσ, a, ha, hp, hpi⟩
  obtain ⟨y, _, hiy⟩ := ff.2.1 i hi
  have eq : y = b := ((sat i y).mp (select i y hiy)).elim
    (fun hy => unique i y b hy hib) (fun h => (h.1 ⟨b, value_bound i b hib, hib⟩).elim)
  have hbμ := eq ▸ bound i y hiy
  exact ⟨ordinal_down_l (ZF.modelsKP hZF) (hκ.mem ha) (φord.mem hμ)
    (hσ.ordinal_le_l hZF owner.omega hU owner.transitive hm hn ⟨p, hp, hpσ⟩ (hκ.mem ha)) hbμ, hbμ⟩

end YesMetaZFC.SetTheory.LargeCardinal
