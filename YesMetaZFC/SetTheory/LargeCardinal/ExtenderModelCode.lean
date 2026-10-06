import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelationCode

/-! # 从实际小枚举自动编码并搬运传递模型

给定源内的任意 A→B 双射图，把 B 的隶属关系拉回 A×A，再在源中实际分离
关系码。A=κ 时，有限幂一致性将此码送到另一源；在那里计算 Mostowski 塌缩，
唯一性识别出原来的 B。调用者只提供实际枚举，无需另给关系码或良基证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_transitive_code_l {ω κ K X R A B F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hB : M.TransitiveSet B) (hF : M.mem F X) (bij : M.IsSetBijectionFromTo I F A B) :
    ∃ T, M.mem T X ∧
      (∀ p, M.mem p T → ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ KPair_d M p a b) ∧ Wc_iso_d A T B F := by
  have hf := fn0_of_function_l (ZF.modelsKP hZF) bij.1.1
  obtain ⟨_, C, hCX, hfc⟩ := source.function_l hZF hF
    (hf.retarget_l fun a b hab => (rd_entry_transitive_l source.transitive hF hab).2)
  obtain ⟨c, hc⟩ := source.code
  have hAX := sc_function_domain_mem_l hZF source.omega source.transitive hc source.theory hF hf
  obtain ⟨P, hPX, hP⟩ := source.square_l hZF hAX
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases C (fun _ => F)), fun _ => A⟩
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (Formula.existsMem (.bound 4) (Formula.existsMem (.bound 5)
        (.conj (kpair0_m (.bound 4) (.bound 3) (.bound 2))
          (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 7))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 7)) (.mem (.bound 1) .newest))))))) }
  have sat p : φ.denote ρ p ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ ∃ x, M.mem x C ∧ ∃ y, M.mem y C ∧
      KPair_d M p a b ∧ Rd_entry_d a x F ∧ Rd_entry_d b y F ∧ M.mem x y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨T, hTX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.mem _ _))))))))
    ρ (Fin.cases hAX (Fin.cases hCX (fun _ => hF))) hPX
  refine ⟨T, hTX, fun p hp => (hP p).mp ((spec p).mp hp).1,
    ⟨hB, hf, bij.2, fun a _ b _ x _ => bij.1.2 a b x, ?_⟩⟩
  intro a ha b hb x hx y hy hax hby
  constructor
  · rintro ⟨p, hp, hpT⟩
    obtain ⟨a', _, b', _, v, _, w, _, hq, hav, hbw, hvw⟩ := (sat p).mp ((spec p).mp hpT).2
    obtain ⟨ea, eb⟩ := kpair_injective_l M hq hp
    exact bij.1.1.1.2 a v x (ea ▸ hav) hax ▸ bij.1.1.1.2 b w y (eb ▸ hbw) hby ▸ hvw
  · intro hxy
    obtain ⟨p, _, hp⟩ := source.kpair_l hZF (source.transitive A hAX a ha) (source.transitive A hAX b hb)
    exact ⟨p, hp, (spec p).mpr ⟨(hP p).mpr ⟨a, ha, b, hb, hp⟩,
      (sat p).mpr ⟨a, ha, b, hb, x, (hfc.bound_l hax).2, y, (hfc.bound_l hby).2, hp, hax, hby, hxy⟩⟩⟩

/-- 小传递模型的跨源还原：关系码、目标内塌缩及其与 B 的相等均自动证明。 -/
theorem Ea_subset_d.transitive_l {ω κ K X R K' Y S B F : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (hB : M.TransitiveSet B)
    (hF : M.mem F X) (bij : M.IsSetBijectionFromTo I F κ B) : M.mem B Y := by
  obtain ⟨T, hT, bound, iso⟩ := ep_transitive_code_l hZF source hB hF bij
  exact subsets.collapse_l hZF source target hT bound iso

end YesMetaZFC.SetTheory.LargeCardinal
