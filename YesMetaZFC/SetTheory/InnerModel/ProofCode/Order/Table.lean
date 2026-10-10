import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Decode
import YesMetaZFC.SetTheory.Ord.OrderType

/-! # 规范码序在集合上的完整关系表

合法码名集合的笛卡尔积上，正反 Σ₁ 证书互补，故 KP 的 Δ₁ 分离产生实际
比较表。它满足仓库已有的集合编码良序接口。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def pn_pair_s (φ : S1_binary 0) : Delta0BinarySchema 1 where
  body := Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 2) <|
    .conj (kpair0_m (.bound 4) (.bound 2) (.bound 1)) (φ.matrix_m Fin.elim0 (.bound 2) (.bound 1) .newest)
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (φ.matrix.delta0.bind_l _))))

theorem pn_pair_sat_l (hKP : M.Models KP) (φ : S1_binary 0) (ρ : Env M 1) (p : M.Domain) :
    (∃ T, (pn_pair_s φ).toBinarySchema.denote ρ p T) ↔
      ∃ v, M.mem v (ρ.bound 0) ∧ ∃ w, M.mem w (ρ.bound 0) ∧ KPair_d M p v w ∧ φ.schema.denote (jh_env_l p) v w := by
  simp only [BinarySchema.denote, pn_pair_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hKP.1, po_matrix_env_l φ (jh_env_l p)]
  change (∃ T v, M.mem v (ρ.bound 0) ∧ ∃ w, M.mem w (ρ.bound 0) ∧ ∃ W, M.mem W T ∧
    KPair_d M p v w ∧ φ.matrix_binary.toBinarySchema.denote ((jh_env_l p).push v) w W) ↔ _
  constructor
  · rintro ⟨T, v, hv, w, hw, W, _, hp, hφ⟩
    exact ⟨v, hv, w, hw, hp, (φ.sat_l (jh_env_l p) v w).mpr ⟨W, hφ⟩⟩
  · rintro ⟨v, hv, w, hw, hp, hφ⟩
    obtain ⟨W, hφ⟩ := (φ.sat_l (jh_env_l p) v w).mp hφ
    obtain ⟨T, ht⟩ := KP.exists_pair hKP W W
    exact ⟨T, v, hv, w, hw, W, (ht W).mpr (Or.inl rfl), hp, hφ⟩

theorem pn_pair_at_l (hKP : M.Models KP) (φ : S1_binary 0) (ρ : Env M 1) {p v w : M.Domain}
    (hv : M.mem v (ρ.bound 0)) (hw : M.mem w (ρ.bound 0)) (hp : KPair_d M p v w) :
    (∃ T, (pn_pair_s φ).toBinarySchema.denote ρ p T) ↔ φ.schema.denote (jh_env_l p) v w := by
  rw [pn_pair_sat_l hKP]
  refine ⟨?_, fun h => ⟨v, hv, w, hw, hp, h⟩⟩
  rintro ⟨x, _, y, _, he, h⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M he hp
  exact h

def Pn_table_d (X R : M.Domain) : Prop :=
  ∀ p, M.mem p R ↔ ∃ v, M.mem v X ∧ ∃ w, M.mem w X ∧ KPair_d M p v w ∧ Pn_lt_d v w

theorem pn_table_exists_l (hM : M.Models KPi) {X : M.Domain} (hv : ∀ v, M.mem v X → Pn_valid_d v) :
    ∃ R, Pn_table_d X R := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := (jh_env_l X).push X
  obtain ⟨P, hp⟩ := KP.kprod_exists_l hKP X X
  obtain ⟨R, hr⟩ := KP.d1_separation_l hKP (pn_pair_s pn_lt_s) (pn_pair_s pn_not_lt_s) ρ P (by
    intro p hpP
    obtain ⟨v, hvX, w, hwX, hpair⟩ := (hp p).mp hpP
    rw [pn_pair_at_l hKP pn_lt_s ρ hvX hwX hpair, pn_pair_at_l hKP pn_not_lt_s ρ hvX hwX hpair]
    exact pn_delta1_l hM (hv v hvX) (hv w hwX) (jh_env_l p))
  refine ⟨R, fun p => ?_⟩
  rw [hr p, pn_pair_sat_l hKP pn_lt_s]
  simp only [pn_lt_sat_l hKP]
  exact ⟨And.right, fun h => ⟨h.elim (fun v hv => hv.2.elim (fun w hw => (hp p).mpr ⟨v, hv.1, w, hw.1, hw.2.1⟩)), h⟩⟩

theorem Pn_table_d.entry_l (hKP : M.Models KP) {X R v w : M.Domain} (hr : Pn_table_d X R) :
    Rd_entry_d v w R ↔ M.mem v X ∧ M.mem w X ∧ Pn_lt_d v w := by
  constructor
  · rintro ⟨p, hp, hpR⟩
    obtain ⟨x, hx, y, hy, he, h⟩ := (hr p).mp hpR
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M he hp
    exact ⟨hx, hy, h⟩
  · rintro ⟨hv, hw, h⟩
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total v w
    exact ⟨p, hp, (hr p).mpr ⟨v, hv, w, hw, hp, h⟩⟩

theorem pn_table_unique_l (hE : Extensional M) {X R S : M.Domain} (hr : Pn_table_d X R) (hs : Pn_table_d X S) : R = S :=
  hE.eq_of_same_members R S (fun p => (hr p).trans (hs p).symm)

theorem Pn_table_d.wellorder_l (hM : M.Models KPi) {X R : M.Domain} (hv : ∀ v, M.mem v X → Pn_valid_d v)
    (hr : Pn_table_d X R) : M.IsSetCodedWellOrder (kp_pair_l (KPi.models_iff_l.mp hM).1) R X := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have entry v w : M.PairMember (kp_pair_l hKP) v w R ↔ M.mem v X ∧ M.mem w X ∧ Pn_lt_d v w := hr.entry_l hKP
  refine ⟨⟨?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨v, _, w, _, hp, _⟩ := (hr p).mp hp
    exact ⟨v, w, hp⟩
  · intro v hvX h
    exact pn_irrefl_l hM (hv v hvX) ((entry v v).mp h).2.2
  · intro u hu v hvX w hw h g
    exact (entry u w).mpr ⟨hu, hw, pn_trans_l hM (hv u hu) (hv v hvX) (hv w hw)
      ((entry u v).mp h).2.2 ((entry v w).mp g).2.2⟩
  · intro v hvX w hwX
    rcases pn_compare_l hM (hv v hvX) (hv w hwX) with he | he | he
    · exact Or.inl (he ▸ (fun _ => Iff.rfl))
    · exact Or.inr (Or.inl ((entry v w).mpr ⟨hvX, hwX, he⟩))
    · exact Or.inr (Or.inr ((entry w v).mpr ⟨hwX, hvX, he⟩))
  · intro Y hy hn
    obtain ⟨v, hvY, hm⟩ := pn_min_l hM (fun v hvY => hv v (hy v hvY)) hn
    exact ⟨v, hvY, fun w hwY => (hm w hwY).elim (fun he => Or.inl (he ▸ (fun _ => Iff.rfl)))
      (fun he => Or.inr ((entry v w).mpr ⟨hy v hvY, hy w hwY, he⟩))⟩

/-- 自动构造指定合法码族上的规范良序表，同时返回已有的集合良序实例。 -/
theorem pn_order_table_l (hM : M.Models KPi) {X : M.Domain} (hv : ∀ v, M.mem v X → Pn_valid_d v) :
    ∃ R, Pn_table_d X R ∧ M.IsSetCodedWellOrder (kp_pair_l (KPi.models_iff_l.mp hM).1) R X := by
  obtain ⟨R, hr⟩ := pn_table_exists_l hM hv
  exact ⟨R, hr, hr.wellorder_l hM hv⟩

/-- 在指定的合法码族中，构造某个合法名字的精确前段。 -/
theorem pn_initial_in_l (hM : M.Models KPi) {X w : M.Domain}
    (hx : ∀ v, M.mem v X → Pn_valid_d v) (hw : Pn_valid_d w) :
    ∃ I, ∀ v, M.mem v I ↔ M.mem v X ∧ Pn_lt_d v w := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨U, hu⟩ := KP.exists_insert hKP X w
  obtain ⟨R, hr⟩ := pn_table_exists_l hM (X := U)
    (fun v hv => ((hu v).mp hv).elim (hx v) (fun he => he.symm ▸ hw))
  let ρ := ((jh_env_l R).push w).push R
  let φ : Delta0UnarySchema 2 := { body := rd_entry0_m .newest (.bound 2) (.bound 1), delta0 := rd_entry0_delta_l .. }
  obtain ⟨I, hi⟩ := KP.separation_exists_d hKP φ ρ X
  refine ⟨I, fun v => (hi v).trans ?_⟩
  apply and_congr_right
  intro hv
  have sat : Formula.satisfies (ρ.push v) φ.body ↔ Rd_entry_d v w R := rd_entry0_sat_l hKP.1 _ _ _ _
  rw [sat, hr.entry_l hKP]
  exact ⟨fun h => h.2.2, fun h => ⟨(hu v).mpr (Or.inl hv), (hu w).mpr (Or.inr rfl), h⟩⟩

end YesMetaZFC.SetTheory.InnerModel
