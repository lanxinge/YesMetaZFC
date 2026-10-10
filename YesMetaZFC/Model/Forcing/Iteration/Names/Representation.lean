import YesMetaZFC.Model.Forcing.Iteration.Stage.Next

/-! # 给定坐标后继的实际重编码图

从现有 Row_repr_d 恢复二步条件到坐标条件的集合双射，而不是重新选择后继
偏序。双射同时保持和反射原序，为固定 N 的主条件搬运提供实际实例。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_repr_map_l (hZF : M.Models ZF) {α t B R z b A T W C S D V}
    (h : Two_step_d M B R z b A T W C S) (hrow : ∀ p, M.mem p B → Row_d M α p)
    (k : Row_repr_d M α t C S D V) : ∃ F,
    M.IsSetBijectionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F C D ∧
    (∀ c q, Entry_d M c q F ↔ M.mem c C ∧ Row_code_d M α t c q) ∧
    ∀ c d p q, Entry_d M c p F → Entry_d M d q F → (Entry_d M p q V ↔ Entry_d M c d S) := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 2 := (⟨fun _ => α, fun _ => α⟩ : Env M 1).push t
  let φ : BinarySchema 2 := { body := row_code_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ c q : φ.denote ρ c q ↔ Row_code_d M α t c q := row_code_sat_l hZF.1 _ _ _ _ _
  have total c (hc : M.mem c C) : ∃ q, φ.denote ρ c q := by
    obtain ⟨p, s, hcp, _, _, _⟩ := (h.conditions c).mp hc
    obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
    exact ⟨q, (hφ c q).mpr ⟨p, s, hcp, hq⟩⟩
  have unique c (_ : M.mem c C) q r (hq : φ.denote ρ c q) (hr : φ.denote ρ c r) : q = r := by
    obtain ⟨p, s, hp, hq⟩ := (hφ c q).mp hq
    obtain ⟨p', s', hp', hr⟩ := (hφ c r).mp hr
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact row_append_unique_l M hZF.1 hq hr
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun c q hc hq => (k.conditions q).mpr ⟨c, hc, (hφ c q).mp hq⟩)
  have edge c q : Entry_d M c q F ↔ M.mem c C ∧ Row_code_d M α t c q :=
    (hf c q).trans (and_congr_right fun _ => hφ c q)
  have inj c d q (hcq : Entry_d M c q F) (hdq : Entry_d M d q F) : c = d := by
    obtain ⟨hc, p, s, hcp, hpq⟩ := (edge c q).mp hcq
    obtain ⟨hd, p', s', hdp, hp'q⟩ := (edge d q).mp hdq
    obtain ⟨rfl, rfl⟩ := row_append_injective_l hZF.1 (KP.mem_irrefl_d (ZF.modelsKP hZF) α)
      (hrow p ((two_step_mem_l h hcp).mp hc).2.1.1)
      (hrow p' ((two_step_mem_l h hdp).mp hd).2.1.1) hpq hp'q
    exact kpair_unique_l M hZF.1 hcp hdp
  refine ⟨F, ⟨⟨hF, inj⟩, fun q hq => ?_⟩, edge, fun c d p q hcp hdq => ?_⟩
  · obtain ⟨c, hc, hcq⟩ := (k.conditions q).mp hq
    exact ⟨c, hc, (edge c q).mpr ⟨hc, hcq⟩⟩
  · constructor
    · intro hpq
      obtain ⟨a, b, ha, hb, hap, hbq, hab⟩ := (k.relation p q).mp hpq
      have hac := inj a c p ((edge a p).mpr ⟨ha, hap⟩) hcp
      have hbd := inj b d q ((edge b q).mpr ⟨hb, hbq⟩) hdq
      exact hac ▸ hbd ▸ hab
    · intro hcd
      obtain ⟨hc, hcp⟩ := (edge c p).mp hcp
      obtain ⟨hd, hdq⟩ := (edge d q).mp hdq
      exact (k.relation p q).mpr ⟨c, d, hc, hd, hcp, hdq, hcd⟩

/-- 已有坐标阶段的预序自动反射到其实际二步表示。 -/
theorem row_repr_order_l (hZF : M.Models ZF) {α t B R z b A T W C S D V}
    (h : Two_step_d M B R z b A T W C S) (hrow : ∀ p, M.mem p B → Row_d M α p)
    (k : Row_repr_d M α t C S D V) (L : Cond_order_d M D V D) : Cond_order_d M C S C := by
  obtain ⟨F, hF, _, he⟩ := row_repr_map_l hZF h hrow k
  have fn := hF.1.1
  refine ⟨fun c hc => ?_, fun c d a hc hd ha hcd hda => ?_, fun c _ hc => ?_⟩
  · obtain ⟨p, hp, hcp⟩ := fn.2.2 c hc
    exact (he c c p p hcp hcp).mp (L.refl p hp)
  · obtain ⟨p, hp, hcp⟩ := fn.2.2 c hc
    obtain ⟨q, hq, hdq⟩ := fn.2.2 d hd
    obtain ⟨r, hr, har⟩ := fn.2.2 a ha
    exact (he c a p r hcp har).mp (L.trans p q r hp hq hr
      ((he c d p q hcp hdq).mpr hcd) ((he d a q r hdq har).mpr hda))
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) C ((h.relation c C).mp hc).2.1).elim

end YesMetaZFC.Model.Forcing.Internal
