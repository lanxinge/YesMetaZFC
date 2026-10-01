import YesMetaZFC.Model.Forcing.CCC.Basic

/-! # 内部阶段嵌入与极大反链

映射使用地模型内的实际函数图。每个目标条件具有一个源条件作为约减，保证
源极大反链的模型内映像仍为极大反链。二步迭代在 `TwoStepEmbedding` 给出实例。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Red_d (R Q S w F x p : M.Domain) : Prop :=
  ∀ q y, Entry_d M q y F → Entry_d M q p R → Cmp_d M Q S w x y

structure Reg_embed_d (P R z Q S w F : M.Domain) : Prop where
  graph : ∀ a, M.mem a F → ∃ p x, KPair_d M a p x
  total : ∀ p, M.mem p P → p ≠ z → ∃ x, Entry_d M p x F
  domain : ∀ p x, Entry_d M p x F → M.mem p P ∧ p ≠ z ∧ M.mem x Q ∧ x ≠ w
  functional : ∀ p x y, Entry_d M p x F → Entry_d M p y F → x = y
  injective : ∀ p q x, Entry_d M p x F → Entry_d M q x F → p = q
  order : ∀ p q x y, Entry_d M p x F → Entry_d M q y F →
    (Entry_d M x y S ↔ Entry_d M p q R)
  compat : ∀ p q x y, Entry_d M p x F → Entry_d M q y F →
    (Cmp_d M Q S w x y ↔ Cmp_d M P R z p q)
  reduction : ∀ x, M.mem x Q → x ≠ w → ∃ p, M.mem p P ∧ p ≠ z ∧
    Red_d M R Q S w F x p

def Max_antichain_d (P R z D : M.Domain) : Prop :=
  Antichain_d M P R z D ∧ ∀ p, M.mem p P → p ≠ z → ∃ q, M.mem q D ∧ Cmp_d M P R z p q

variable {M} {P R z Q S w F : M.Domain}

/-- 最大条件的单元素集给出原 ZF 内可直接构造的极大反链实例。 -/
theorem top_antichain_l (O : Cond_order_d M P R z) (hPair : ∀ a b, ∃ D, Pair_d M D a b)
    {t} (ht : M.mem t P) (hz : t ≠ z)
    (hTop : ∀ p, M.mem p P → p ≠ z → Entry_d M p t R) : ∃ D, Max_antichain_d M P R z D := by
  obtain ⟨D, hD⟩ := hPair t t
  have eq {p} (hp : M.mem p D) : p = t := ((hD p).mp hp).elim id id
  refine ⟨D, ⟨fun p hp => eq hp ▸ ⟨ht, hz⟩,
    fun p q hp hq _ => (eq hp).trans (eq hq).symm⟩, fun p hp hpz => ?_⟩
  exact ⟨t, (hD t).mpr (Or.inl rfl), p, below_refl_l O hp hpz, hTop p hp hpz⟩

/-- 极大反链保持使用实际分离像；不预设目标稠密集能直接回拉成源稠密集。 -/
theorem reg_embed_max_l (hZF : M.Models ZF) (L : Cond_order_d M Q S w)
    (h : Reg_embed_d M P R z Q S w F) {D} (hD : Max_antichain_d M P R z D) :
    ∃ E, (∀ x, M.mem x E ↔ ∃ p, M.mem p D ∧ Entry_d M p x F) ∧ Max_antichain_d M Q S w E := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push D
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2))
    (entry_m .newest (.bound 1) (.bound 3))) }
  obtain ⟨E, hE⟩ := ZF.separation_exists_d hZF φ ρ Q
  have image x : M.mem x E ↔ ∃ p, M.mem p D ∧ Entry_d M p x F := by
    rw [hE x]
    have he : φ.denote ρ x ↔ ∃ p, M.mem p D ∧ Entry_d M p x F := by
      simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff,
        Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, entry_sat_l M hZF.1]
      rfl
    change (M.mem x Q ∧ φ.denote ρ x) ↔ _
    rw [he]
    exact ⟨And.right, fun hp => ⟨hp.elim fun p hp => (h.domain p x hp.2).2.2.1, hp⟩⟩
  refine ⟨E, image, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, _, hp⟩ := (image x).mp hx
    exact (h.domain p x hp).2.2
  · intro x y hx hy hxy
    obtain ⟨p, hpD, hpx⟩ := (image x).mp hx
    obtain ⟨q, hqD, hqy⟩ := (image y).mp hy
    have he := hD.1.2 p q hpD hqD ((h.compat p q x y hpx hqy).mp hxy)
    subst q
    exact h.functional p x y hpx hqy
  · intro x hx hxw
    obtain ⟨p, hp, hpz, hr⟩ := h.reduction x hx hxw
    obtain ⟨q, hqD, r, hrp, hrq⟩ := hD.2 p hp hpz
    obtain ⟨v, hrv⟩ := h.total r hrp.1 hrp.2.1
    obtain ⟨y, hqy⟩ := h.total q (hD.1.1 q hqD).1 (hD.1.1 q hqD).2
    obtain ⟨s, hsx, hsv⟩ := hr r v hrv hrp.2.2
    have hvy := (h.order r q v y hrv hqy).mpr hrq
    exact ⟨y, (image y).mpr ⟨q, hqD, hqy⟩, s, hsx,
      L.trans s v y hsx.1 (h.domain r v hrv).2.2.1 (h.domain q y hqy).2.2.1 hsv hvy⟩

end YesMetaZFC.Model.Forcing.Internal
