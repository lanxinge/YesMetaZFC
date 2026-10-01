import YesMetaZFC.SetTheory.InnerModel.ProofCode.Construction
import YesMetaZFC.SetTheory.InnerModel.Jensen.Model

/-! # 构造码恰好覆盖 J 内对象

先对 rudimentary 迭代证明码的封闭性，再沿 J 层级的内部序数归纳证明覆盖。
反方向按推导高度归纳；不存在把可编码性或覆盖性写入模型接口的附加假设。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pc_coded_d (x : M.Domain) : Prop := ∃ c, Pc_eval_d c x

def pc_coded_m {n} (x : Term n) : Formula 1 n := .existsE (pc_eval_m .newest x.weaken)
derive_free_closed pc_coded_m

theorem pc_coded_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (pc_coded_m x) ↔ Pc_coded_d (x.eval ρ) := by
  simp only [pc_coded_m, Pc_coded_d, Formula.satisfies_exists_iff, pc_eval_formula_l hKP,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem pc_closed_l (hM : M.Models KPi) (k : Rd_sym) {a b c x : M.Domain}
    (ha : Pc_coded_d a) (hb : Pc_coded_d b) (hc : Pc_coded_d c) (hx : Rd_fun_d k a b c x) : Pc_coded_d x := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  obtain ⟨r, hr⟩ := hc
  obtain ⟨d, _, _, hd⟩ := pc_apply_exists_l hM k hp hq hr hx
  exact ⟨d, hd⟩

theorem pc_rd_iter_l (hM : M.Models KPi) {U a Y : M.Domain}
    (hu : ∀ x, M.mem x U → Pc_coded_d x) (hy : Rd_iter_d U a Y) : ∀ x, M.mem x Y → Pc_coded_d x := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ψ : UnarySchema 1 := { body := .forallE (.imp (rd_iter_m (.bound 2) (.bound 1) .newest)
    (Formula.forallMem .newest (pc_coded_m .newest))) }
  have hψ b : ψ.denote (rd_seed_env_l U) b ↔ ∀ V, Rd_iter_d U b V → ∀ x, M.mem x V → Pc_coded_d x := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_iter_sat_l hKP.1, Formula.satisfies_forallMem_iff, pc_coded_sat_l hKP]
    rfl
  apply (hψ a).mp (hi ψ (rd_seed_env_l U) ?_ a) Y hy
  intro b ih
  apply (hψ b).mpr
  intro V hv x hx
  obtain ⟨H, hs, hh⟩ := rd_iter_equation_l hM hv
  have hc t (ht : M.mem t H) : Pc_coded_d t := ((hh t).mp ht).elim (hu t)
    (fun ⟨d, hd, W, hw, ht⟩ => (hψ d).mp (ih d hd) W hw t ht)
  exact ((hs x).mp hx).elim (hc x) (fun ⟨k, a, b, c, ha, hb, hd, h⟩ => pc_closed_l hM k (hc a ha) (hc b hb) (hc c hd) h)

theorem pc_jh_cover_l (hM : M.Models KPi) {a Y : M.Domain} (ha : M.IsOrdinal a) (hy : Jh_value_d a Y) :
    ∀ x, M.mem x Y → Pc_coded_d x := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ψ : UnarySchema 0 := { body := .imp (KP.ord0_m .newest) (.forallE
    (.imp (jh_value_m (.bound 1) .newest) (Formula.forallMem .newest (pc_coded_m .newest)))) }
  have hψ b : ψ.denote (jh_env_l a) b ↔
      (M.IsOrdinal b → ∀ V, Jh_value_d b V → ∀ x, M.mem x V → Pc_coded_d x) := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP,
      Formula.satisfies_forall_iff, jh_value_sat_l, Formula.satisfies_forallMem_iff, pc_coded_sat_l hKP]
    rfl
  apply (hψ a).mp (hi ψ (jh_env_l a) ?_ a) ha Y hy
  intro b ih
  apply (hψ b).mpr
  intro hb V hv x hx
  obtain ⟨d, hd, A, hA, Z, ⟨S, hs, ω, _, hz⟩, hx⟩ := (jh_value_equation_l hM hv x).mp hx
  have cover : ∀ t, M.mem t S → Pc_coded_d t := by
    intro t ht
    rcases (hs t).mp ht with ht | he
    · exact (hψ d).mp (ih d hd) (hb.mem hd) A hA t ht
    · obtain ⟨c, _, _, hc⟩ := pc_leaf_exists_l hM (hb.mem hd) hA
      exact (hKP.1.eq_of_same_members t A he).symm ▸ (show Pc_coded_d A from ⟨c, hc⟩)
  exact pc_rd_iter_l hM cover hz x hx

theorem pc_eval_in_l_l (hM : M.Models KPi) {c x : M.Domain} (hx : Pc_eval_d c x) : L_d x := by
  obtain ⟨h, hx⟩ := hx
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ψ : UnarySchema 0 := { body := .forallE (.forallE (.imp
    (pc_rank_m (.bound 2) (.bound 1) .newest) (l_m .newest))) }
  have hψ n : ψ.denote (jh_env_l h) n ↔ ∀ c x, Pc_rank_d n c x → L_d x := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      pc_rank_formula_l hKP, l_sat_l hKP]
    rfl
  apply (hψ h).mp (hi ψ (jh_env_l h) ?_ h) c x hx
  intro n ih
  apply (hψ n).mpr
  rintro c x ⟨T, F, hf, hx⟩
  have child {d y} (hy : Pc_read_d F n d y) : L_d y := by
    obtain ⟨m, hm, hy⟩ := hy
    exact (hψ m).mp (ih m hm) d y ⟨T, F, hf, hy⟩
  rcases (hf.at_l hx).2.2.2.2 with ⟨a, _, _, ha, W, _, hw⟩ | ⟨k, a, _, b, _, d, _, u, _, v, _, w, _, _, ha, hb, hd, hx⟩
  · exact l_layer_l hM ⟨ha, (pc_jh_value_l a x).mp ⟨W, hw⟩⟩
  · exact l_closed_l hM k (child ha) (child hb) (child hd) hx

theorem pc_coded_iff_l (hM : M.Models KPi) (x : M.Domain) : Pc_coded_d x ↔ L_d x :=
  ⟨fun ⟨_, h⟩ => pc_eval_in_l_l hM h, fun ⟨_, _, ha, hx⟩ => pc_jh_cover_l hM ha.1 ha.2 x hx⟩

end YesMetaZFC.SetTheory.InnerModel
