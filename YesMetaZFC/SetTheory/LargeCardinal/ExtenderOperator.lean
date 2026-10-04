import YesMetaZFC.SetTheory.LargeCardinal.MeasureConstraints

/-! # 从测度族构造扩展器算子

E(A) 中的支撑恰为其测度集中在 A 上的支撑。输入允许混合有限长度；
整个 E 是定义于全部有限列空间幂集上的实际函数图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_value_d (F S A B : M.Domain) : Prop := ∀ a, M.mem a B ↔ M.mem a S ∧
  ∃ U D, Rd_entry_d a U F ∧ M.mem D U ∧ M.MemberSubset D A

def ex_value_m {d} (F S A B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest S.weaken) (.existsE (.existsE (.conj
    (rd_entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.conj (.mem .newest (.bound 1))
      (Formula.subset .newest A.weaken.weaken.weaken)))))))
derive_free_closed ex_value_m

theorem ex_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (F S A B : Term d) :
    Formula.satisfies ρ (ex_value_m F S A B) ↔ Ex_value_d (F.eval ρ) (S.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [ex_value_m, Ex_value_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    rd_entry_sat_l hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def Ex_operator_d (K S F E : M.Domain) : Prop := ∃ P Q, M.IsPowerSetOf P K ∧ M.IsPowerSetOf Q S ∧
  Fn0_d P Q E ∧ ∀ A B, Rd_entry_d A B E ↔ M.mem A P ∧ Ex_value_d F S A B

theorem ex_operator_exists_l (hZF : M.Models ZF) (K S F : M.Domain) : ∃ E, Ex_operator_d K S F E := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF K
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF S
  let ρ := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push S
  let φ : BinarySchema 2 := { body := ex_value_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat A B : φ.denote ρ A B ↔ Ex_value_d F S A B := ex_value_sat_l hZF.1 _ _ _ _ _
  obtain ⟨E, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := Q)
    (fun A _ => by
      let η := ρ.push A
      let ψ : UnarySchema 3 := { body := .existsE (.existsE (.conj
        (rd_entry_m (.bound 2) (.bound 1) (.bound 5))
        (.conj (.mem .newest (.bound 1)) (Formula.subset .newest (.bound 3))))) }
      obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF ψ η S
      refine ⟨B, (sat A B).mpr fun a => ?_⟩
      simpa only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry_sat_l hZF.1,
        Formula.satisfies_mem_iff, Formula.satisfies_subset_iff] using! hb a)
    (fun A _ B C hb hc => hZF.1.eq_of_same_members B C fun a => ((sat A B).mp hb a).trans ((sat A C).mp hc a).symm)
    (fun A B _ hb => (hQ B).mpr fun a ha => (((sat A B).mp hb a).mp ha).1)
  exact ⟨E, P, Q, hP, hQ, fn0_of_function_l (ZF.modelsKP hZF) he,
    fun A B => (spec A B).trans (and_congr_right fun _ => sat A B)⟩

theorem Ex_operator_d.at_l {K S F E A B : M.Domain} (h : Ex_operator_d K S F E)
    (hab : Rd_entry_d A B E) : M.MemberSubset A K ∧ Ex_value_d F S A B := by
  obtain ⟨_, _, hp, _, _, hs⟩ := h
  exact ⟨(hp A).mp ((hs A B).mp hab).1, ((hs A B).mp hab).2⟩

theorem Ex_operator_d.total_l {K S F E A : M.Domain} (h : Ex_operator_d K S F E)
    (ha : M.MemberSubset A K) : ∃ B, Rd_entry_d A B E := by
  obtain ⟨_, _, hp, _, he, _⟩ := h
  exact (he.2.1 A ((hp A).mpr ha)).imp fun _ hh => hh.2

theorem ex_value_at_l (hE : Extensional M) {ω κ L F S n a U A B : M.Domain}
    (hF : Em_family_d ω κ L F) (haS : M.mem a S) (ha : Fn0_d n L a) (haU : Rd_entry_d a U F)
    (hA : ∀ s, M.mem s A → Fn0_d n κ s) (hv : Ex_value_d F S A B) : M.mem a B ↔ M.mem A U := by
  obtain ⟨m, D, _, hm, hd, hu⟩ := hF.measure a U haU
  have e := hm.domain_eq_l hE ha
  subst m
  exact (hv a).trans ⟨fun ⟨_, V, C, haV, hc, hCA⟩ =>
      hu.1.2.2.1 C A (hF.function a V U haV haU ▸ hc) hCA (fun s hs => (hd s).mpr (hA s hs)),
    fun h => ⟨haS, U, A, haU, h, fun _ => id⟩⟩

theorem ex_value_type_l (hE : Extensional M) {ω κ L F S n A B : M.Domain}
    (hF : Em_family_d ω κ L F) (hA : ∀ s, M.mem s A → Fn0_d n κ s)
    (hv : Ex_value_d F S A B) : ∀ a, M.mem a B → Fn0_d n L a := by
  intro a ha
  obtain ⟨_, U, T, hu, ht, sub⟩ := (hv a).mp ha
  obtain ⟨m, D, _, hm, hd, hU⟩ := hF.measure a U hu
  obtain ⟨s, hs⟩ := hU.2.1 T ht
  have e := ((hd s).mp (hU.1.1 T ht s hs)).domain_eq_l hE (hA s (sub s hs))
  exact e ▸ hm

end YesMetaZFC.SetTheory.LargeCardinal
