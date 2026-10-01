import YesMetaZFC.Model.Forcing.Iteration.Stage.Basic
import YesMetaZFC.Model.Forcing.Internal.Functions.Generic

/-! # 任意阶段在指定前缀泛型下的旧条件名称

给 N 中的旧条件 r 的规范名称赋以 r↾α 为权重，得到真正的商条件集名称。
所有条件与名称均在原模型内取值；没有指定外部泛型或枚举 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_quot_d (I : kpair_convention_l.Interpretation M) (α B b D N K : M.Domain) : Prop := Name_d M B K ∧
  ∀ v a, Entry_d M v a K ↔ M.mem a B ∧
    ∃ r, M.mem r D ∧ M.mem r N ∧ M.IsRestrictionOf I a r α ∧ Check_d M b r v

def row_quot_m {n} (α B b D N K : Term n) : Formula 1 n :=
  .conj (name_m B K) (.forallE (.forallE (.iff (entry_m (.bound 1) .newest K.weaken.weaken)
    (.conj (.mem .newest B.weaken.weaken) (.existsE
      (.conj (.mem .newest D.weaken.weaken.weaken)
        (.conj (.mem .newest N.weaken.weaken.weaken)
          (.conj (Formula.isRestriction kpair_convention_l (.bound 1) .newest α.weaken.weaken.weaken)
            (check_m b.weaken.weaken.weaken .newest (.bound 2))))))))))
derive_free_closed row_quot_m

theorem row_quot_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B b D N K : Term n) : Formula.satisfies ρ (row_quot_m α B b D N K) ↔
      Row_quot_d I (α.eval ρ) (B.eval ρ) (b.eval ρ) (D.eval ρ) (N.eval ρ) (K.eval ρ) := by
  simp only [row_quot_m, Row_quot_d, Formula.satisfies_conj_iff, name_sat_l M hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, entry_sat_l M hE,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_isRestriction_iff I,
    check_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

/-- 商条件名称由旧条件和前缀唯一确定，不需要选择名称或商代表。 -/
theorem row_quot_exists_l (hZF : M.Models ZF) {B b} (hb : M.mem b B) (α D N : M.Domain) :
    ∃ K, Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hX, hn⟩ := check_image_l hZF hb D
  let ρ : Env M 4 := (((⟨fun _ => α, fun _ => α⟩ : Env M 1).push b).push D).push N
  let φ : BinarySchema 4 := {
    body := .existsE (.conj (.mem .newest (.bound 4)) (.conj (.mem .newest (.bound 3))
      (.conj (Formula.isRestriction kpair_convention_l (.bound 1) .newest (.bound 6))
        (check_m (.bound 5) .newest (.bound 2))))) }
  have hφ v a : φ.denote ρ v a ↔
      ∃ r, M.mem r D ∧ M.mem r N ∧ M.IsRestrictionOf I a r α ∧ Check_d M b r v := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_isRestriction_iff I, check_sat_l M hZF.1]
    rfl
  obtain ⟨K, hK, _, he⟩ := name_comp_l M hZF φ ρ B X hn
  refine ⟨K, hK, fun v a => (he v a).trans ?_⟩
  exact ⟨fun h => ⟨h.2.1, (hφ v a).mp h.2.2⟩, fun h =>
    ⟨(hX v).mpr (h.2.elim fun r h => ⟨r, h.1, h.2.2.2⟩),
      h.1, (hφ v a).mpr h.2⟩⟩

theorem row_quot_unique_l (hE : Extensional M) {I : kpair_convention_l.Interpretation M} {α B b D N K L}
    (hK : Row_quot_d I α B b D N K) (hL : Row_quot_d I α B b D N L) : K = L := by
  have rel {v} (hv : Name_d M B v) : ∀ x, M.mem x v → ∃ a b, KPair_d M x a b := by
    obtain ⟨W, hv, hW⟩ := hv
    exact fun x hx => (hW v hv x hx).elim fun a h => h.elim fun b h => ⟨a, b, h.1⟩
  exact entry_ext_l M hE (rel hK.1) (rel hL.1) (fun v a => (hK.2 v a).trans (hL.2 v a).symm)

def Row_dec_d (I : kpair_convention_l.Interpretation M) (α B R b D N τ c r a v : M.Domain) : Prop :=
  M.mem r D ∧ M.mem r N ∧ M.mem a B ∧ M.IsRestrictionOf I a r α ∧
    Check_d M b r v ∧ Below_d M B R B c a ∧ Eq_force_d M B R B c τ v

def row_dec_m {n} (α B R b D N τ c r a v : Term n) : Formula 1 n :=
  .conj (.mem r D) (.conj (.mem r N) (.conj (.mem a B)
    (.conj (Formula.isRestriction kpair_convention_l a r α) (.conj (check_m b r v)
      (.conj (below_m B R B c a) (eq_force_m B R B c τ v))))))
derive_free_closed row_dec_m

theorem row_dec_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R b D N τ c r a v : Term n) : Formula.satisfies ρ (row_dec_m α B R b D N τ c r a v) ↔
      Row_dec_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (N.eval ρ)
        (τ.eval ρ) (c.eval ρ) (r.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [row_dec_m, Row_dec_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRestriction_iff I, check_sat_l M hE, below_sat_l M hE, eq_force_sat_l M hE]

/-- 任意阶段的商成员力迫直接给出稠密的旧条件决定分支。 -/
theorem row_quot_decide_l {I : kpair_convention_l.Interpretation M} {α B R b D N K τ p}
    (hK : Row_quot_d I α B b D N K) (hτ : Mem_force_d M B R B p τ K) :
    Dense_d M B R B (fun c => ∃ r a v, Row_dec_d I α B R b D N τ c r a v) p := by
  intro q hq
  obtain ⟨c, v, a, hcq, hva, hca, he⟩ := hτ.2 q hq
  obtain ⟨ha, r, hr, hrN, har, hv⟩ := (hK.2 v a).mp hva
  exact ⟨c, hcq, r, a, v, hr, hrN, ha, har, hv, ⟨hcq.1, hcq.2.1, hca⟩, he⟩

/-- 旧条件的规范名称给出商条件名称的实际实例。 -/
theorem row_quot_check_l (hZF : M.Models ZF) {I : kpair_convention_l.Interpretation M} {α B R b D N K r a v p}
    (O : Cond_order_d M B R B) (hb : M.mem b B) (hK : Row_quot_d I α B b D N K)
    (hr : M.mem r D) (hrN : M.mem r N) (ha : M.mem a B) (har : M.IsRestrictionOf I a r α)
    (hv : Check_d M b r v) (hp : M.mem p B) (hpa : Entry_d M p a R) :
    Mem_force_d M B R B p v K :=
  mem_force_entry_l O hZF hp (check_name_l M (check_range_l M hZF) hb hv) ha
    ((hK.2 v a).mpr ⟨ha, r, hr, hrN, har, hv⟩) hpa

/-- 商条件名称被迫取值于每个包含 D∩N 的旧集合。 -/
theorem row_quot_subset_l (hZF : M.Models ZF) {I : kpair_convention_l.Interpretation M} {α B R b D N K X ν τ p}
    (O : Cond_order_d M B R B) (hb : M.mem b B) (hK : Row_quot_d I α B b D N K)
    (hX : ∀ r, M.mem r D → M.mem r N → M.mem r X)
    (hν : Check_d M b X ν) (hpb : Entry_d M p b R) (hτ : Mem_force_d M B R B p τ K) :
    Mem_force_d M B R B p τ ν := by
  refine ⟨hτ.1, fun q hq => ?_⟩
  obtain ⟨r, t, a, hrq, hta, _, he⟩ := hτ.2 q hq
  obtain ⟨_, s, hsD, hsN, _, hst⟩ := (hK.2 t a).mp hta
  have htb := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hν t b).mpr
    ⟨rfl, s, hX s hsD hsN, hst⟩
  exact ⟨r, t, b, hrq, htb, O.trans r p b hrq.1 hτ.1 hb (below_trans_l O hτ.1 hrq hq).2.2 hpb, he⟩

/-- 泛型值恰是 N 中前缀被该泛型接受的旧条件，没有额外条件混入。 -/
theorem row_quot_value_l (hZF : M.Models ZF) {I : kpair_convention_l.Interpretation M} {α B R b D N K U}
    (O : Cond_order_d M B R B) (hU : Generic_d M B R B U)
    (hK : Row_quot_d I α B b D N K)
    {Y : (extension_l M hZF B R B U).Domain} (hY : Qval_d M B R B U K Y)
    (e : M.Domain → (extension_l M hZF B R B U).Domain)
    (he : ∀ r v, Check_d M b r v → Qval_d M B R B U v (e r))
    (x : (extension_l M hZF B R B U).Domain) :
    x ∈ Y ↔ ∃ r a, M.mem r D ∧ M.mem r N ∧ M.IsRestrictionOf I a r α ∧ U a ∧ e r = x := by
  rw [qval_mem_l O hZF hU hY]
  constructor
  · rintro ⟨v, a, hva, ha, hv⟩
    obtain ⟨_, r, hr, hrN, har, hrv⟩ := (hK.2 v a).mp hva
    exact ⟨r, a, hr, hrN, har, ha, qval_unique_l (he r v hrv) hv⟩
  · rintro ⟨r, a, hr, hrN, har, ha, rfl⟩
    obtain ⟨v, hv⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b r
    exact ⟨v, a, (hK.2 v a).mpr ⟨(hU.proper a ha).1, r, hr, hrN, har, hv⟩, ha, he r v hv⟩

/-- 真实后继表示反射任意已有追加的两个坐标及其成员力迫。 -/
theorem row_repr_decode_l (hZF : M.Models ZF) {α B R e A T t W C S D V r a s}
    (h : Row_stage_d M α B R e) (hStep : Two_step_d M B R B e A T W C S)
    (k : Row_repr_d M α t C S D V) (hr : M.mem r D) (ha : M.mem a B)
    (har : Row_append_d M α t a s r) :
    M.mem s W ∧ Mem_force_d M B R B a s A ∧ ∃ x, M.mem x C ∧ KPair_d M x a s := by
  obtain ⟨x, hx, a', s', hxa, har'⟩ := (k.conditions r).mp hr
  have hh := (two_step_mem_l hStep hxa).mp hx
  obtain ⟨he, hs⟩ := row_append_injective_l hZF.1 (KP.mem_irrefl_d (ZF.modelsKP hZF) α)
    (h.rows a ha) (h.rows a' hh.2.1.1) har har'
  subst a' s'
  exact ⟨hh.1, hh.2.2, x, hx, hxa⟩

end YesMetaZFC.Model.Forcing.Internal
