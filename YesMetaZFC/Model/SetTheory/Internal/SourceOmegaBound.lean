import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOrdinal
import YesMetaZFC.SetTheory.Card.SmallBound

/-! # 模型内的不可数共尾性及其初等保持

只记录本步真正需要的性质：模型中的每张 ω→δ 图都在 δ 内有严格界。
原正则基数给出实际实例，整条全称句子的初等保持覆盖目标中新出现的图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_omega_bound_d (ω X δ : M.Domain) : Prop := ∀ f, M.mem f X → Fn0_d ω δ f →
  ∃ β, M.mem β δ ∧ ∀ n y, Rd_entry_d n y f → M.mem y β

def sc_omega_bound_m {n} (ω δ f : Term n) : Formula 1 n := .imp (fn0_m ω δ f)
  (Formula.existsMem δ (Formula.forallMem ω.weaken (Formula.forallMem δ.weaken.weaken
    (.imp (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken) (.mem .newest (.bound 2))))))
derive_free_closed sc_omega_bound_m

theorem sc_omega_bound_delta_l {n} (ω δ f : Term n) : (sc_omega_bound_m ω δ f).IsDelta0 :=
  .imp (fn0_delta_l ..) (.existsMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.mem _ _)))))

theorem sc_omega_bound_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω δ f : Term n) :
    Formula.satisfies ρ (sc_omega_bound_m ω δ f) ↔ (Fn0_d (ω.eval ρ) (δ.eval ρ) (f.eval ρ) →
      ∃ β, M.mem β (δ.eval ρ) ∧ ∀ i y, Rd_entry_d i y (f.eval ρ) → M.mem y β) := by
  simp only [sc_omega_bound_m, Formula.satisfies_imp_iff, fn0_sat_l hE, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h hf => (h hf).imp fun β hb => ⟨hb.1, fun i y hy => hb.2 i (hf.bound_l hy).1 y (hf.bound_l hy).2 hy⟩,
    fun h hf => (h hf).imp fun β hb => ⟨hb.1, fun i _ y _ hy => hb.2 i y hy⟩⟩

theorem sc_regular_bound_l (hZF : M.Models ZF) {ω δ : M.Domain}
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) δ) (hωδ : M.mem ω δ) (X : M.Domain) :
    Sc_omega_bound_d ω X δ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro f _ hf
  have fn := fn0_function_l (ZF.modelsKP hZF) hf
  obtain ⟨A, ha⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  obtain ⟨β, hβ, bound⟩ := (hr.range_bounded_of_domain_mem hZF I hωδ fn ha).exists_bound
  obtain ⟨γ, hγ, hβγ⟩ := hr.isLimitOrdinal.2.2 β hβ
  exact ⟨γ, hγ, fun i y hy => (bound y ((ha y).mpr ⟨i, hy⟩)).elim
    (fun eq => eq.symm ▸ hβγ) ((hr.isCardinal.1.mem hγ).transitive β hβγ y)⟩

theorem smap_omega_bound_l (hZF : M.Models ZF) {ω c d X R Y S j δ ε : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hωX : M.mem ω X) (hδε : Rd_entry_d δ ε j) :
    Sc_omega_bound_d ω X δ ↔ Sc_omega_bound_d ω Y ε := by
  have tr := hj.forall_delta_l hZF hω hX hY hm hn (n := 2) (sc_omega_bound_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (sc_omega_bound_delta_l ..)
    ⟨Fin.cases δ (fun _ => ω), fun _ => ω⟩ ⟨Fin.cases ε (fun _ => ω), fun _ => ω⟩
    (Fin.cases hδε (fun _ => hj.omega_l _ hZF hω hX hY hm hn hωX))
  simpa only [sc_omega_bound_sat_l hZF.1] using! tr

end YesMetaZFC.SetTheory.Internal
