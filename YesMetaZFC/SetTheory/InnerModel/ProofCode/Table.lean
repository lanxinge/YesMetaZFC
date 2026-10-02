import YesMetaZFC.SetTheory.InnerModel.ProofCode.Erasure

/-! # 合法码集合上的完整 Σ₁ 求值表

表中包含每个输入码的值，且没有额外条目。这个完整性结论使后续最小码
检查可以只遍历已集合化的候选域，而不在全宇宙中否定另一条 Σ₁ 求值关系。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def pc_named_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (pc_cert_m (.bound 1) (.bound 3)) (.conj (pc_at_m (.bound 1) (.bound 2) (.bound 5) .newest)
        (kpair0_m (.bound 4) (.bound 5) .newest)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (pc_cert_delta_l ..)
      (.conj (pc_at_delta_l ..) (kpair0_delta_l ..))))) }

theorem pc_named_sat_l (hKP : M.Models KP) (ρ : Env M 0) (c p : M.Domain) :
    pc_named_s.schema.denote ρ c p ↔ ∃ x, Pc_eval_d c x ∧ KPair_d M p c x := by
  rw [S1_binary.sat_l]
  simp only [pc_named_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pc_cert_sat_l hKP, pc_at_sat_l hKP.1, kpair0_sat_l hKP.1]
  change (∃ T h, M.mem h T ∧ ∃ F, M.mem F T ∧ ∃ x, M.mem x T ∧ Pc_cert_d F T ∧ Pc_at_d F h c x ∧ KPair_d M p c x) ↔ _
  exact ⟨fun ⟨T, h, _, F, _, x, _, hf, hx, hp⟩ => ⟨x, ⟨h, T, F, hf, hx⟩, hp⟩,
    fun ⟨x, ⟨h, T, F, hf, hx⟩, hp⟩ => ⟨T, h, (hf.at_l hx).1, F, hf.graph, x, (hf.at_l hx).2.2.1, hf, hx, hp⟩⟩

def Pc_table_d (C F : M.Domain) : Prop :=
  ∀ p, M.mem p F ↔ ∃ c, M.mem c C ∧ ∃ x, Pc_eval_d c x ∧ KPair_d M p c x

def pc_table_s : S1_binary 0 := pc_named_s.image

theorem pc_table_sat_l (hM : M.Models KPi) (ρ : Env M 0) (C F : M.Domain)
    (hc : ∀ c, M.mem c C → Ps_valid_d c) : pc_table_s.schema.denote ρ C F ↔ Pc_table_d C F := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [pc_table_s, S1_binary.image_sat_l hKP]
  · simp only [pc_named_sat_l hKP]; rfl
  · intro c h
    obtain ⟨x, hx⟩ := ps_eval_total_l hM (hc c h)
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total c x
    exact ⟨p, (pc_named_sat_l hKP ρ c p).mpr ⟨x, hx, hp⟩⟩
  · intro c _ p q hp hq
    obtain ⟨x, hx, hp⟩ := (pc_named_sat_l hKP ρ c p).mp hp
    obtain ⟨y, hy, hq⟩ := (pc_named_sat_l hKP ρ c q).mp hq
    have he := pc_eval_unique_l hM hx hy; subst y
    exact kpair_unique_l M hKP.1 hp hq

theorem pc_table_exists_l (hM : M.Models KPi) (C : M.Domain) (hc : ∀ c, M.mem c C → Ps_valid_d c) :
    ∃ F, Pc_table_d C F := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := jh_env_l C
  obtain ⟨F, hf⟩ := KP.s1_image_l hKP pc_named_s ρ C (by
    intro c h
    obtain ⟨x, hx⟩ := ps_eval_total_l hM (hc c h)
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total c x
    exact ⟨p, (pc_named_sat_l hKP ρ c p).mpr ⟨x, hx, hp⟩⟩) (by
    intro c _ p q hp hq
    obtain ⟨x, hx, hp⟩ := (pc_named_sat_l hKP ρ c p).mp hp
    obtain ⟨y, hy, hq⟩ := (pc_named_sat_l hKP ρ c q).mp hq
    have he := pc_eval_unique_l hM hx hy; subst y
    exact kpair_unique_l M hKP.1 hp hq)
  exact ⟨F, fun p => (hf p).trans (exists_congr fun c => and_congr_right fun _ => pc_named_sat_l hKP ρ c p)⟩

theorem Pc_table_d.entry_l {C F c x : M.Domain} (hf : Pc_table_d C F) :
    Rd_entry_d c x F ↔ M.mem c C ∧ Pc_eval_d c x := by
  constructor
  · rintro ⟨p, hp, hpf⟩
    obtain ⟨d, hd, y, hy, hg⟩ := (hf p).mp hpf
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hg hp
    exact ⟨hd, hy⟩
  · rintro ⟨hc, n, T, G, hg, r, hr, p, hp, hrc⟩
    exact ⟨p, hp, (hf p).mpr ⟨c, hc, x, ⟨n, T, G, hg, r, hr, p, hp, hrc⟩, hp⟩⟩

theorem pc_table_unique_l (hE : Extensional M) {C F G : M.Domain} (hf : Pc_table_d C F) (hg : Pc_table_d C G) : F = G :=
  hE.eq_of_same_members F G (fun p => (hf p).trans (hg p).symm)

end YesMetaZFC.SetTheory.InnerModel
