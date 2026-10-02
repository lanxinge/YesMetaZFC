import YesMetaZFC.SetTheory.InnerModel.Recursion.Cover

/-! # KPi 中Σ₁ 全函数的成员递归

对各成员收集实际证书，取兼容函数图的并；必要时加入当前输入的一行。
证书的一致性先于存在性证明，因此这里不进行外部选择或外部良基递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rc_value_exists_l (hM : M.Models KPi) {n} (φ : S1_binary n) (ρ : Env M n)
    (ht : ∀ F, ∃ y, φ.schema.denote ρ F y)
    (hu : ∀ F y z, φ.schema.denote ρ F y → φ.schema.denote ρ F z → y = z)
    (x : M.Domain) : ∃ y, Rc_value_d φ ρ x y := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let I := kp_pair_l hKP
  let ψ : UnarySchema n := {
    body := .existsE (binary_pred_m (rc_value_s φ).schema
      (fun i => .bound ⟨i.val + 2, by omega⟩) (.bound 1) .newest) }
  have hψ a : ψ.denote ρ a ↔ ∃ y, Rc_value_d φ ρ a y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_exists_iff, binary_pred_sat_l, rc_value_sat_l hKP.1]
    rfl
  apply (hψ x).mp (hi ψ ρ ?_ x)
  intro x ih
  apply (hψ x).mpr
  obtain ⟨B, hB⟩ := KP.s1_collection_l hKP (rc_value_s φ) ρ x (fun a ha =>
    ((hψ a).mp (ih a ha)).imp (fun y hy => (rc_value_sat_l hKP.1 φ ρ a y).mpr hy))
  obtain ⟨C, hC⟩ := KP.exists_union hKP B
  let η := ρ.push B
  let χ : Delta0UnarySchema (n + 1) := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem .newest
      (rc_cert_m φ (fun i => .bound ⟨i.val + 4, by omega⟩) .newest (.bound 2) (.bound 1)))
    freeClosed := by simp -implicitDefEqProofs
    delta0 := .existsMem _ (.existsMem _ (rc_cert_delta_l ..)) }
  have hχ F : χ.toUnarySchema.denote η F ↔ ∃ T, M.mem T B ∧ ∃ A, M.mem A T ∧ Rc_cert_d φ ρ A F T := by
    simp only [UnarySchema.denote, χ, Formula.satisfies_existsMem_iff, rc_cert_sat_l hKP.1]
    rfl
  obtain ⟨P, hP'⟩ := KP.separation_exists_d hKP χ η C
  have hP F : M.mem F P ↔ ∃ T, M.mem T B ∧ ∃ A, Rc_cert_d φ ρ A F T := by
    rw [hP' F, show Formula.satisfies (η.push F) χ.body ↔ _ from hχ F]
    exact ⟨fun ⟨_, T, hT, A, _, h⟩ => ⟨T, hT, A, h⟩,
      fun ⟨T, hT, A, h⟩ => ⟨(hC F).mpr ⟨T, hT, h.graph⟩, T, hT, A, h.domain, h⟩⟩
  obtain ⟨G, hG⟩ := KP.exists_union hKP P
  have entry a b : Rd_entry_d a b G ↔ ∃ F, M.mem F P ∧ Rd_entry_d a b F := by
    constructor
    · rintro ⟨p, hp, hpg⟩
      obtain ⟨F, hF, hpf⟩ := (hG p).mp hpg
      exact ⟨F, hF, p, hp, hpf⟩
    · rintro ⟨F, hF, p, hp, hpf⟩
      exact ⟨p, hp, (hG p).mpr ⟨F, hF, hpf⟩⟩
  have value a b (h : Rd_entry_d a b G) : Rc_value_d φ ρ a b := by
    obtain ⟨F, hF, hf⟩ := (entry a b).mp h
    obtain ⟨T, _, A, h⟩ := (hP F).mp hF
    exact h.value_l hf
  obtain ⟨H, hH, hPH⟩ := KPi.transitive_cover_l hM P
  have bound a b (h : Rd_entry_d a b G) : M.mem a H ∧ M.mem b H := by
    obtain ⟨F, hF, hf⟩ := (entry a b).mp h
    exact rd_entry_transitive_l hH (hH P hPH F hF) hf
  let δ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (rd_entry0_m (.bound 1) .newest (.bound 3))
    delta0 := .existsMem _ (rd_entry0_delta_l ..) }
  let ν : Env M 2 := (⟨fun _ => G, fun _ => G⟩ : Env M 1).push H
  obtain ⟨D, hD'⟩ := KP.separation_exists_d hKP δ ν H
  have hD a : M.mem a D ↔ ∃ b, Rd_entry_d a b G := by
    rw [hD' a]
    have hd : Formula.satisfies (ν.push a) δ.body ↔ ∃ b, M.mem b H ∧ Rd_entry_d a b G := by
      simp only [δ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hKP.1]
      rfl
    rw [hd]
    exact ⟨fun ⟨_, b, _, h⟩ => ⟨b, h⟩, fun ⟨b, h⟩ => ⟨(bound a b h).1, b, (bound a b h).2, h⟩⟩
  have fn : Fn0_d D H G := by
    refine ⟨?_, fun a ha => ?_, fun a _ b _ c _ hb hc => rc_value_unique_l hM φ ρ hu (value a b hb) (value a c hc)⟩
    · intro p hp
      obtain ⟨F, hFP, hpf⟩ := (hG p).mp hp
      obtain ⟨T, _, A, hF⟩ := (hP F).mp hFP
      obtain ⟨a, _, b, _, hab⟩ := hF.function.1 p hpf
      have he : Rd_entry_d a b G := ⟨p, hab, hp⟩
      exact ⟨a, (hD a).mpr ⟨b, he⟩, b, (bound a b he).2, hab⟩
    · obtain ⟨b, hb⟩ := (hD a).mp ha
      exact ⟨b, (bound a b hb).2, hb⟩
  have trans : M.TransitiveSet D := by
    intro a ha b hb
    obtain ⟨v, hv⟩ := (hD a).mp ha
    obtain ⟨F, hFP, haf⟩ := (entry a v).mp hv
    obtain ⟨T, _, A, hF⟩ := (hP F).mp hFP
    obtain ⟨w, _, hw⟩ := hF.function.2.1 b (hF.hereditary a (hF.function.bound_l haf).1 b hb)
    exact (hD b).mpr ⟨w, (entry b w).mpr ⟨F, hFP, hw⟩⟩
  have children : M.MemberSubset x D := by
    intro a ha
    obtain ⟨y, _, T, hTB, hc⟩ := hB a ha
    obtain ⟨A, F, hF, _, hy⟩ := (rc_matrix_sat_l hKP.1 φ ρ a y T).mp hc
    exact (hD a).mpr ⟨y, (entry a y).mpr ⟨F, (hP F).mpr ⟨T, hTB, A, hF⟩, hy⟩⟩
  have step a y (hy : Rd_entry_d a y G) :
      ∃ R, M.IsRestrictionOf I R G a ∧ φ.schema.denote ρ R y := by
    obtain ⟨F, hFP, haf⟩ := (entry a y).mp hy
    obtain ⟨T, _, A, hF⟩ := (hP F).mp hFP
    obtain ⟨R, _, hr, hp⟩ := hF.step a (hF.function.bound_l haf).1
    have hRF := res0_restriction_l hKP hF.function hr
    obtain ⟨w, _, hw⟩ := hp y (hF.function.bound_l haf).2 haf
    refine ⟨R, ⟨hRF.1, fun b c => (hRF.2 b c).trans (and_congr_right fun hb => ?_)⟩,
      (φ.sat_l ρ R y).mpr ⟨w, hw⟩⟩
    constructor
    · exact fun h => (entry b c).mpr ⟨F, hFP, h⟩
    · intro h
      obtain ⟨v, _, hv⟩ := hF.function.2.1 b (hF.hereditary a (hF.function.bound_l haf).1 b hb)
      have he := rc_value_unique_l hM φ ρ hu (value b c h) (hF.value_l hv)
      exact he.symm ▸ hv
  classical
  by_cases hx : M.mem x D
  · obtain ⟨y, _, hy⟩ := fn.2.1 x hx
    exact ⟨y, value x y hy⟩
  · obtain ⟨R, hR⟩ := res0_exists_l hKP G x H
    have hRG := res0_restriction_l hKP fn hR
    obtain ⟨y, hy⟩ := ht R
    obtain ⟨p, hp⟩ := I.total x y
    obtain ⟨F, hF⟩ := KP.exists_insert hKP G p
    obtain ⟨A, hA⟩ := KP.exists_insert hKP D x
    obtain ⟨T, hT⟩ := KP.exists_insert hKP H y
    have entries a b : Rd_entry_d a b F ↔ Rd_entry_d a b G ∨ (a = x ∧ b = y) := by
      constructor
      · rintro ⟨q, hq, hqF⟩
        rcases (hF q).mp hqF with hqG | rfl
        · exact Or.inl ⟨q, hq, hqG⟩
        · exact Or.inr (kpair_injective_l M hq hp)
      · rintro (⟨q, hq, hqG⟩ | ⟨rfl, rfl⟩)
        · exact ⟨q, hq, (hF q).mpr (Or.inl hqG)⟩
        · exact ⟨p, hp, (hF p).mpr (Or.inr rfl)⟩
    have fn' : Fn0_d A T F := by
      refine ⟨?_, ?_, fun a _ b _ c _ hb hc => ?_⟩
      · intro q hq
        rcases (hF q).mp hq with hq | rfl
        · obtain ⟨a, ha, b, hb, hq⟩ := fn.1 q hq
          exact ⟨a, (hA a).mpr (Or.inl ha), b, (hT b).mpr (Or.inl hb), hq⟩
        · exact ⟨x, (hA x).mpr (Or.inr rfl), y, (hT y).mpr (Or.inr rfl), hp⟩
      · intro a ha
        rcases (hA a).mp ha with ha | he
        · obtain ⟨b, hb, he⟩ := fn.2.1 a ha
          exact ⟨b, (hT b).mpr (Or.inl hb), (entries a b).mpr (Or.inl he)⟩
        · exact ⟨y, (hT y).mpr (Or.inr rfl), (entries a y).mpr (Or.inr ⟨he, rfl⟩)⟩
      · rcases (entries a b).mp hb with hb | hb <;>
          rcases (entries a c).mp hc with hc | hc
        · exact rc_value_unique_l hM φ ρ hu (value a b hb) (value a c hc)
        · exact (hx (hc.1 ▸ (fn.bound_l hb).1)).elim
        · exact (hx (hb.1 ▸ (fn.bound_l hc).1)).elim
        · exact hb.2.trans hc.2.symm
    have trans' : M.TransitiveSet A := by
      intro a ha b hb
      exact (hA b).mpr (Or.inl (((hA a).mp ha).elim (fun ha => trans a ha b hb) (fun he => children b (he ▸ hb))))
    have preserve {S a : M.Domain} (hS : M.IsRestrictionOf I S G a) (hn : ¬ M.mem x a) :
        M.IsRestrictionOf I S F a := by
      refine ⟨hS.1, fun b c => (hS.2 b c).trans (and_congr_right fun hb => ?_)⟩
      exact ⟨fun h => (entries b c).mpr (Or.inl h), fun h => ((entries b c).mp h).elim id
        (fun he => (hn (he.1 ▸ hb)).elim)⟩
    obtain ⟨U, hU⟩ := rc_cert_cover_l hM φ ρ trans' fn' (by
      intro a ha v hv
      rcases (hA a).mp ha with ha | he
      · have hvg : Rd_entry_d a v G := ((entries a v).mp hv).elim id (fun he => (hx (he.1 ▸ ha)).elim)
        obtain ⟨S, hS, hs⟩ := step a v hvg
        exact ⟨S, preserve hS (fun h => hx (trans a ha x h)), hs⟩
      · subst a
        have he : v = y := ((entries x v).mp hv).elim (fun h => (hx (fn.bound_l h).1).elim) And.right
        exact ⟨R, preserve hRG (KP.mem_irrefl_d hKP x), he.symm ▸ hy⟩)
    exact ⟨y, U, A, F, hU, (hA x).mpr (Or.inr rfl), (entries x y).mpr (Or.inr ⟨rfl, rfl⟩)⟩

/-- 递归值的前段是实际集合图，且其条目恰好是同一递归关系的前值。 -/
theorem rc_value_equation_l (hM : M.Models KPi) {n} (φ : S1_binary n) (ρ : Env M n)
    (hu : ∀ F y z, φ.schema.denote ρ F y → φ.schema.denote ρ F z → y = z)
    {a Y : M.Domain} (hy : Rc_value_d φ ρ a Y) : ∃ G,
      M.IsSetRelation (kp_pair_l (KPi.models_iff_l.mp hM).1) G ∧ φ.schema.denote ρ G Y ∧
        ∀ b v, Rd_entry_d b v G ↔ M.mem b a ∧ Rc_value_d φ ρ b v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨T, A, F, hf, ha, hay⟩ := hy
  obtain ⟨G, _, hg, hgφ⟩ := hf.step a ha
  obtain ⟨w, _, hw⟩ := hgφ Y (hf.function.bound_l hay).2 hay
  have hgF := res0_restriction_l hKP hf.function hg
  refine ⟨G, hgF.1, (φ.sat_l ρ G Y).mpr ⟨w, hw⟩, fun b v => (hgF.2 b v).trans ?_⟩
  refine ⟨fun ⟨hb, hv⟩ => ⟨hb, hf.value_l hv⟩, fun ⟨hb, hv⟩ => ?_⟩
  obtain ⟨z, _, hz⟩ := hf.function.2.1 b (hf.hereditary a ha b hb)
  have he := rc_value_unique_l hM φ ρ hu hv (hf.value_l hz)
  exact ⟨hb, he.symm ▸ hz⟩

end YesMetaZFC.SetTheory.InnerModel
