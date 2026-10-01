import YesMetaZFC.SetTheory.InnerModel.ProofCode.Table

/-! # 构造集族的集合大小编码域

Σ₁ 收集同时收集码与求值证书，随后只用 Δ₀ 分离筛掉额外对象。
所得实际求值表满射到给定集合，不使用外部选择函数。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def pc_code_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (pc_cert_m .newest (.bound 2)) (pc_at_m .newest (.bound 1) (.bound 3) (.bound 4))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (pc_cert_delta_l ..) (pc_at_delta_l ..))) }

theorem pc_code_sat_l (hKP : M.Models KP) (ρ : Env M 0) (x c : M.Domain) :
    pc_code_s.schema.denote ρ x c ↔ Pc_eval_d c x := by
  rw [S1_binary.sat_l]
  simp only [pc_code_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pc_cert_sat_l hKP, pc_at_sat_l hKP.1]
  change (∃ T h, M.mem h T ∧ ∃ F, M.mem F T ∧ Pc_cert_d F T ∧ Pc_at_d F h c x) ↔ _
  exact ⟨fun ⟨T, h, _, F, _, hf, hx⟩ => ⟨h, T, F, hf, hx⟩,
    fun ⟨h, T, F, hf, hx⟩ => ⟨T, h, (hf.at_l hx).1, F, hf.graph, hf, hx⟩⟩

theorem pc_set_cover_l (hM : M.Models KPi) (X : M.Domain) (hx : ∀ x, M.mem x X → L_d x) :
    ∃ C F, Pc_table_d C F ∧ Fn0_d C X F ∧ ∀ x, M.mem x X → ∃ c, M.mem c C ∧ Rd_entry_d c x F := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let η := jh_env_l X
  obtain ⟨B, hb⟩ := KP.s1_collection_l hKP pc_code_s η X (by
    intro x h
    obtain ⟨c, hc⟩ := (pc_coded_iff_l hM x).mpr (hx x h)
    exact ⟨c, (pc_code_sat_l hKP η x c).mpr hc⟩)
  let e : Fin 3 → Fin 5 := Fin.cases 0 (Fin.cases 2 (fun _ => 1))
  let ρ := (η.push X).push B
  let δ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2) (pc_code_s.matrix.body.rename e))
    freeClosed := by simp -implicitDefEqProofs [pc_code_s.matrix.freeClosed]
    delta0 := .existsMem _ (.existsMem _ (pc_code_s.matrix.delta0.rename_l e)) }
  have he c x w : (((ρ.push c).push x).push w).reindex e = ((η.push x).push c).push w := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))), rfl⟩
  have hδ c : δ.toUnarySchema.denote ρ c ↔ ∃ x, M.mem x X ∧ ∃ w, M.mem w B ∧
      Formula.satisfies (((η.push x).push c).push w) pc_code_s.matrix.body := by
    simp only [UnarySchema.denote, δ, Formula.satisfies_existsMem_iff, Formula.satisfies_rename, he]
    rfl
  obtain ⟨C, hC⟩ := KP.separation_exists_d hKP δ ρ B
  have source c (hc : M.mem c C) : ∃ x, M.mem x X ∧ Pc_eval_d c x := by
    obtain ⟨x, hx, w, _, hw⟩ := (hδ c).mp ((hC c).mp hc).2
    exact ⟨x, hx, (pc_code_sat_l hKP η x c).mp ((pc_code_s.sat_l η x c).mpr ⟨w, hw⟩)⟩
  have onto x (hx : M.mem x X) : ∃ c, M.mem c C ∧ Pc_eval_d c x := by
    obtain ⟨c, hc, w, hwB, hw⟩ := hb x hx
    exact ⟨c, (hC c).mpr ⟨hc, (hδ c).mpr ⟨x, hx, w, hwB, hw⟩⟩,
      (pc_code_sat_l hKP η x c).mp ((pc_code_s.sat_l η x c).mpr ⟨w, hw⟩)⟩
  obtain ⟨F, hf⟩ := pc_table_exists_l hM C (fun c hc => (source c hc).elim fun _ h => pc_eval_valid_l hKP h.2)
  have bound {c x} (hc : M.mem c C) (he : Pc_eval_d c x) : M.mem x X := by
    obtain ⟨y, hy, h⟩ := source c hc
    exact pc_eval_unique_l hM h he ▸ hy
  refine ⟨C, F, hf, ⟨?_, ?_, ?_⟩, fun x hx => ?_⟩
  · intro p hp
    obtain ⟨c, hc, x, hx, hp⟩ := (hf p).mp hp
    exact ⟨c, hc, x, bound hc hx, hp⟩
  · intro c hc
    obtain ⟨x, hx, h⟩ := source c hc
    exact ⟨x, hx, hf.entry_l.mpr ⟨hc, h⟩⟩
  · intro c _ x _ y _ hx hy
    exact pc_eval_unique_l hM (hf.entry_l.mp hx).2 (hf.entry_l.mp hy).2
  · obtain ⟨c, hc, he⟩ := onto x hx
    exact ⟨c, hc, hf.entry_l.mpr ⟨hc, he⟩⟩

end YesMetaZFC.SetTheory.InnerModel
