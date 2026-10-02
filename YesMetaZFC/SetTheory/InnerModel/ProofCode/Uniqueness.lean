import YesMetaZFC.SetTheory.InnerModel.ProofCode.Certificate

/-! # 同一码的求值一致性

对第一份推导的内部高度归纳，同时允许第二份推导有任意高度。
由此证书的函数性是结论，而不依赖外部良基性或证明码反射假设。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem pc_rank_unique_l (hM : M.Models KPi) {h c x y : M.Domain}
    (hx : Pc_rank_d h c x) (hy : Pc_eval_d c y) : x = y := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ψ : UnarySchema 0 := { body := .forallE (.forallE (.forallE (.imp
    (.conj (pc_rank_m (.bound 3) (.bound 2) (.bound 1)) (pc_eval_m (.bound 2) .newest))
      (Formula.extensionalEq (.bound 1) .newest)))) }
  have hψ n : ψ.denote (jh_env_l h) n ↔ ∀ c x y, Pc_rank_d n c x → Pc_eval_d c y → x = y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, pc_rank_formula_l hKP, pc_eval_formula_l hKP,
      Formula.satisfies_extensionalEq_iff_eq hKP.1]
    exact ⟨fun h c x y hx hy => h c x y ⟨hx, hy⟩, fun h c x y ⟨hx, hy⟩ => h c x y hx hy⟩
  apply (hψ h).mp (hi ψ (jh_env_l h) ?_ h) c x y hx hy
  intro n ih
  apply (hψ n).mpr
  rintro c x y ⟨T, F, hF, hx⟩ ⟨m, U, G, hG, hy⟩
  have agree {d u v} (hu : Pc_read_d F n d u) (hv : Pc_read_d G m d v) : u = v := by
    obtain ⟨i, hi, hu⟩ := hu
    obtain ⟨j, _, hv⟩ := hv
    exact (hψ i).mp (ih i hi) d u v ⟨T, F, hF, hu⟩ ⟨j, U, G, hG, hv⟩
  rcases (hF.at_l hx).2.2.2.2 with hx | ⟨k, hx⟩ <;>
    rcases (hG.at_l hy).2.2.2.2 with hy | ⟨l, hy⟩
  · obtain ⟨a, _, hc, _, W, _, hx⟩ := hx
    obtain ⟨b, _, hd, _, V, _, hy⟩ := hy
    have he := pc_leaf_inj_l hc hd; subst b
    exact jh_value_unique_l hM ((pc_jh_value_l a x).mp ⟨W, hx⟩) ((pc_jh_value_l a y).mp ⟨V, hy⟩)
  · obtain ⟨a, _, hc, _⟩ := hx
    obtain ⟨b, _, d, _, e, _, u, _, v, _, w, _, hd, _⟩ := hy
    exact (pc_leaf_node_false_l hKP hc hd).elim
  · obtain ⟨a, _, b, _, d, _, u, _, v, _, w, _, hc, _⟩ := hx
    obtain ⟨e, _, hd, _⟩ := hy
    exact (pc_leaf_node_false_l hKP hd hc).elim
  · obtain ⟨a, _, b, _, d, _, u, _, v, _, w, _, hc, ha, hb, hd, hx⟩ := hx
    obtain ⟨a', _, b', _, d', _, u', _, v', _, w', _, he, ha', hb', hd', hy⟩ := hy
    obtain ⟨rfl, rfl, rfl, rfl⟩ := pc_node_inj_l hKP hc he
    have hu := agree ha ha'; subst u'
    have hv := agree hb hb'; subst v'
    have hw := agree hd hd'; subst w'
    exact rd_fun_unique_l hKP.1 hx hy

theorem pc_eval_unique_l (hM : M.Models KPi) {c x y : M.Domain} (hx : Pc_eval_d c x) (hy : Pc_eval_d c y) : x = y :=
  hx.elim fun _ hx => pc_rank_unique_l hM hx hy

end YesMetaZFC.SetTheory.InnerModel
