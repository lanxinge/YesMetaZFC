import YesMetaZFC.Model.Forcing.Internal.Maximum.Hull
import YesMetaZFC.Model.Forcing.Internal.Maximum.Mixing

/-! # 混合闭合的确定名称库

令 S 为输入名称的最小闭支撑，取 W = 𝒫(S × B)。闭性给出 S ⊆ W；
W 中名称的子名称仍在 S，故任意可定义混合仍在 W。整个构造只使用原 ZF，
幂集、乘积和所有量词都在地模型内部，不要求外部良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

/-- 名称的所有直接条目位于 S × B。 -/
def Name_bound_d (B S t : M.Domain) : Prop :=
  ∀ v, M.mem v t → ∃ a b, KPair_d M v a b ∧ M.mem a S ∧ M.mem b B

def name_bound_m {n} (B S t : Term n) : Formula 1 n :=
  Formula.forallMem t (.existsE (.existsE
    (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.conj (.mem (.bound 1) S.weaken.weaken.weaken) (.mem .newest B.weaken.weaken.weaken)))))
derive_free_closed name_bound_m

theorem name_bound_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B S t : Term n) :
    Formula.satisfies ρ (name_bound_m B S t) ↔
      Name_bound_d M (B.eval ρ) (S.eval ρ) (t.eval ρ) := by
  simp only [name_bound_m, Name_bound_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Name_pool_d (B s t W : M.Domain) : Prop :=
  ∃ S, Name_hull_d M B s t S ∧ ∀ a, M.mem a W ↔ Name_bound_d M B S a

def name_pool_m {n} (B s t W : Term n) : Formula 1 n :=
  .existsE (.conj (name_hull_m B.weaken s.weaken t.weaken .newest)
    (.forallE (.iff (.mem .newest W.weaken.weaken)
      (name_bound_m B.weaken.weaken (.bound 1) .newest))))
derive_free_closed name_pool_m

theorem name_pool_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B s t W : Term n) :
    Formula.satisfies ρ (name_pool_m B s t W) ↔
      Name_pool_d M (B.eval ρ) (s.eval ρ) (t.eval ρ) (W.eval ρ) := by
  simp only [name_pool_m, Name_pool_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    name_hull_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, name_bound_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem name_pool_exists_l (hZF : M.Models ZF) {B s t}
    (hs : Name_d M B s) (ht : Name_d M B t) : ∃ W, Name_pool_d M B s t W := by
  obtain ⟨S, hS⟩ := name_hull_exists_l M hZF hs ht
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF X
  refine ⟨W, S, hS, fun a => (hW a).trans ?_⟩
  exact ⟨fun h v hv => by
    obtain ⟨s, hs, b, hb, hp⟩ := (hX v).mp (h v hv)
    exact ⟨s, b, hp, hs, hb⟩, fun h v hv => by
    obtain ⟨s, b, hp, hs, hb⟩ := h v hv
    exact (hX v).mpr ⟨s, hs, b, hb, hp⟩⟩

theorem name_pool_unique_l (hE : Extensional M) {B s t W V}
    (h : Name_pool_d M B s t W) (k : Name_pool_d M B s t V) : W = V := by
  obtain ⟨S, hS, hW⟩ := h
  obtain ⟨T, hT, hV⟩ := k
  have he := name_hull_unique_l M hE hS hT
  subst T
  exact hE.eq_of_same_members W V (fun a => (hW a).trans (hV a).symm)

variable {M} {B s t W : M.Domain}

theorem Name_pool_d.left (h : Name_pool_d M B s t W) : M.mem s W := by
  obtain ⟨S, hS, hW⟩ := h
  exact (hW s).mpr (hS.closed s hS.left)

theorem Name_pool_d.right (h : Name_pool_d M B s t W) : M.mem t W := by
  obtain ⟨S, hS, hW⟩ := h
  exact (hW t).mpr (hS.closed t hS.right)

theorem Name_pool_d.closed (h : Name_pool_d M B s t W) : Supp_d M B W := by
  obtain ⟨S, hS, hW⟩ := h
  intro a ha v hv
  obtain ⟨c, b, hc, hcS, hb⟩ := (hW a).mp ha v hv
  exact ⟨c, b, hc, (hW c).mpr (hS.closed c hcS), hb⟩

/-- 任意名称只要其直接子名称来自库中名称的直接子名称，就仍在同一库中。 -/
theorem Name_pool_d.mem_of_entries (h : Name_pool_d M B s t W) {q}
    (hq : Name_d M B q)
    (hb : ∀ a d, Entry_d M a d q → ∃ r b, M.mem r W ∧ Entry_d M a b r) : M.mem q W := by
  obtain ⟨S, hS, hW⟩ := h
  apply (hW q).mpr
  obtain ⟨V, hqV, hV⟩ := hq
  intro v hv
  obtain ⟨a, d, hvad, _, hd⟩ := hV q hqV v hv
  obtain ⟨r, b, hr, w, hwa, hw⟩ := hb a d ⟨v, hvad, hv⟩
  obtain ⟨a', b', hw', ha, _⟩ := (hW r).mp hr w hw
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hwa hw'
  exact ⟨a, d, hvad, ha, hd⟩

/-- 给定实际公式的相容选择族，其混合名称不离开已装配的名称库。 -/
theorem name_pool_mix_l {R z} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Name_pool_d M B s t W) {n} (φ : BinarySchema n) (ρ : Env M n)
    (hc : ∀ p q a b r, M.mem p B → M.mem q B → M.mem a W → M.mem b W →
      φ.denote ρ a p → φ.denote ρ b q → Below_d M B R z r p → Below_d M B R z r q →
      Eq_force_d M B R z r a b) :
    ∃ a, M.mem a W ∧ ∀ p b, M.mem p B → M.mem b W → φ.denote ρ b p → Eq_force_d M B R z p a b := by
  obtain ⟨a, ha, hb, hm⟩ := mixing_l O hZF φ ρ h.closed hc
  exact ⟨a, h.mem_of_entries ha hb, hm⟩

/-- 被迫属于目标集的任意名称，在同一条件上有库内等值代表；只需 ZF。 -/
theorem name_pool_represent_l {R z v} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Name_pool_d M B s t W) (hv : Name_d M B v) :
    ∃ a, M.mem a W ∧ ∀ p, Mem_force_d M B R z p v s → Eq_force_d M B R z p a v := by
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push v
  let φ : BinarySchema 4 := {
    body := eq_force_m (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1) (.bound 2) }
  have hφ a p : φ.denote ρ a p ↔ Eq_force_d M B R z p a v :=
    eq_force_sat_l M hZF.1 ((ρ.push a).push p) _ _ _ _ _ _
  have hn a (ha : M.mem a W) : Name_d M B a := ⟨W, ha, h.closed⟩
  obtain ⟨a, ha, hm⟩ := name_pool_mix_l O hZF h φ ρ (by
    intro p q a b r hp hq ha hb hpa hqb hrp hrq
    exact eq_force_trans_l O hZF (hn a ha) hv (hn b hb)
      (eq_force_lower_l O hZF (hn a ha) hv p r hp hrp ((hφ a p).mp hpa))
      (eq_force_symm_l hZF (hn b hb) hv
        (eq_force_lower_l O hZF (hn b hb) hv q r hq hrq ((hφ b q).mp hqb))))
  refine ⟨a, ha, fun p hp => eq_force_dense_l O hZF (hn a ha) hv hp.1 ?_⟩
  intro q hq
  obtain ⟨r, b, c, hr, hbc, _, he⟩ := hp.2 q hq
  have hb := (supp_entry_l M h.closed h.left hbc).1
  have he' := eq_force_symm_l hZF hv (hn b hb) he
  exact ⟨r, hr, eq_force_trans_l O hZF (hn a ha) (hn b hb) hv
    (hm r b hr.1 hb ((hφ b r).mpr he')) he'⟩

end YesMetaZFC.Model.Forcing.Internal
