import YesMetaZFC.Model.Forcing.Internal.Forcing.OrderCongruence
import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence
import YesMetaZFC.Model.Forcing.Internal.Extension.Choice

/-! # 任意名称偏序的二步迭代

条件为 (p,s)，其中 p 在给定首阶段条件以下，并迫使 s 属于第二阶段条件集。
第二坐标取自该条件集名称的一个内部闭支撑，因此整个二步条件域是地模型集合。
加强关系为 p≤q 且 p 迫使 s≤t；第二阶段不要求属于地模型的规范名称像。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

private def entry_body_m : Formula 1 3 := entry_m (.bound 1) (.bound 0) (.bound 2)
@[simp] private theorem rel_closed_l : entry_body_m.FreeClosed := entry_m_freeClosed _ _ _ rfl rfl rfl

/-- 关系公式的变量代入统一在原 AST 上完成，供二步序与被迫使的序公理共用。 -/
def rel_at_m {n} (s t T : Term n) : Formula 1 n :=
  entry_body_m.bind (Fin.cases t (Fin.cases s (fun _ => T)))
@[simp] theorem rel_at_closed_l {n} (s t T : Term n)
    (hs : s.freeSupport = []) (ht : t.freeSupport = []) (hT : T.freeSupport = []) : (rel_at_m s t T).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases ht (Fin.cases hs (fun _ => hT))) _).mpr rel_closed_l

theorem rel_at_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (s t T : Term n) :
    Formula.satisfies ρ (rel_at_m s t T) ↔ Entry_d M (s.eval ρ) (t.eval ρ) (T.eval ρ) := by
  simp only [rel_at_m, Formula.satisfies_bind, entry_body_m, entry_sat_l M hE]
  rfl

def Preord_d (M : SetTheory.Structure.{u}) (A T : M.Domain) : Prop :=
  (∀ s, M.mem s A → Entry_d M s s T) ∧
  ∀ s t v, M.mem s A → M.mem t A → M.mem v A → Entry_d M s t T → Entry_d M t v T → Entry_d M s v T

def preord_m {n} (A T : Term n) : Formula 1 n :=
  .conj (.forallE (.imp (.mem .newest A.weaken) (rel_at_m .newest .newest T.weaken)))
    (.forallE (.forallE (.forallE (.imp
      (.conj (.mem (.bound 2) A.weaken.weaken.weaken)
        (.conj (.mem (.bound 1) A.weaken.weaken.weaken)
          (.conj (.mem .newest A.weaken.weaken.weaken)
            (.conj (rel_at_m (.bound 2) (.bound 1) T.weaken.weaken.weaken)
              (rel_at_m (.bound 1) .newest T.weaken.weaken.weaken)))))
      (rel_at_m (.bound 2) .newest T.weaken.weaken.weaken)))))
derive_free_closed preord_m

theorem preord_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (A T : Term n) :
    Formula.satisfies ρ (preord_m A T) ↔ Preord_d M (A.eval ρ) (T.eval ρ) := by
  simp only [preord_m, Preord_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, rel_at_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact and_congr Iff.rfl (forall_congr' fun s => forall_congr' fun t => forall_congr' fun v =>
    ⟨fun h hs ht hv hst htv => h ⟨hs, ht, hv, hst, htv⟩, fun h ⟨hs, ht, hv, hst, htv⟩ => h hs ht hv hst htv⟩)

def cond_order_m {n} (B R z : Term n) : Formula 1 n :=
  .conj (preord_m B R) (.forallE (.imp
    (.conj (.mem .newest B.weaken) (entry_m .newest z.weaken R.weaken))
    (Formula.extensionalEq .newest z.weaken)))
derive_free_closed cond_order_m

theorem cond_order_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (B R z : Term n) :
    Formula.satisfies ρ (cond_order_m B R z) ↔ Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) := by
  simp only [cond_order_m, Formula.satisfies_conj_iff, preord_sat_l hE, Preord_d,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    entry_sat_l M hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1.1, h.1.2, fun p hp hz => h.2 p ⟨hp, hz⟩⟩,
    fun h => ⟨⟨h.refl, h.trans⟩, fun p ⟨hp, hz⟩ => h.zero p hp hz⟩⟩

/-- 限制到条件域的实际关系；域外的无关条目不成为排除值以下的条件。 -/
theorem preord_order_l {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) {Q T : M.Domain}
    (h : Preord_d M Q T) : ∃ D,
      (∀ p q, Entry_d M p q D ↔ M.mem p Q ∧ M.mem q Q ∧ Entry_d M p q T) ∧ Cond_order_d M Q D Q ∧
      (∀ U, Generic_d M Q T Q U ↔ Generic_d M Q D Q U) ∧
      ∀ {a n} (φ : Formula a n) (ρ : Env M n), (∀ t : Term n, Name_d M Q (t.eval ρ)) →
        ∀ p, M.mem p Q → (Forces_d M Q T Q φ ρ p ↔ Forces_d M Q D Q φ ρ p) := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  let φ : BinarySchema 1 := { body := entry_m (.bound 1) .newest (.bound 2) }
  obtain ⟨D, _, hD⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ Q
  have hd p q : Entry_d M p q D ↔ M.mem p Q ∧ M.mem q Q ∧ Entry_d M p q T :=
    (hD p q).trans (and_congr_right fun _ => and_congr_right fun _ => entry_sat_l M hZF.1 _ _ _ _)
  have hc p q (hp : M.mem p Q) (hq : M.mem q Q) : Entry_d M p q T ↔ Entry_d M p q D :=
    ⟨fun he => (hd p q).mpr ⟨hp, hq, he⟩, fun he => ((hd p q).mp he).2.2⟩
  exact ⟨D, hd, {
    refl := fun p hp => (hd p p).mpr ⟨hp, hp, h.1 p hp⟩
    trans := fun p q r hp hq hr hpq hqr => (hd p r).mpr
      ⟨hp, hr, h.2 p q r hp hq hr ((hd p q).mp hpq).2.2 ((hd q r).mp hqr).2.2⟩
    zero := fun p _ hp => False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) Q ((hd p Q).mp hp).2.1) },
    generic_order_l hc, fun φ ρ hn => forces_order_l hc hZF φ ρ hn⟩

variable (M : SetTheory.Structure.{u})

def rel_env_l (T s t : M.Domain) : Env M 3 :=
  ((⟨fun _ => T, fun _ => T⟩ : Env M 1).push s).push t

def ord_env_l (A T : M.Domain) : Env M 2 := (⟨fun _ => T, fun _ => T⟩ : Env M 1).push A

def Rel_force_d (B R z T p s t : M.Domain) : Prop := Forces_d M B R z entry_body_m (rel_env_l M T s t) p

def rel_force_m {n} (B R z T p s t : Term n) : Formula 1 n :=
  force_at_m entry_body_m (Fin.cases t (Fin.cases s (fun _ => T))) B R z p
@[simp] theorem rel_force_closed_l {n} (B R z T p s t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hT : T.freeSupport = []) (hp : p.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) :
    (rel_force_m B R z T p s t).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ rel_closed_l (Fin.cases ht (Fin.cases hs (fun _ => hT))) hB hR hz hp

theorem rel_force_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z T p s t : Term n) :
    Formula.satisfies ρ (rel_force_m B R z T p s t) ↔
      Rel_force_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (T.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  rw [rel_force_m, force_at_sat_l]
  -- 正文自由闭合，故默认自由赋值不影响关系真值。
  apply forces_env_l hE entry_body_m rel_closed_l
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl))

theorem force_rel_at_l (hE : Extensional M) {B R z} {n} (ρ : Env M n) (p : M.Domain) (s t T : Term n) :
    Forces_d M B R z (rel_at_m s t T) ρ p ↔ Rel_force_d M B R z (T.eval ρ) p (s.eval ρ) (t.eval ρ) := by
  rw [rel_at_m, forces_bind_l hE]
  apply forces_env_l hE entry_body_m rel_closed_l
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl))

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z) (hZF : M.Models ZF)

private theorem rel_env_name_l {T s t} (hT : Name_d M B T) (hs : Name_d M B s) (ht : Name_d M B t) :
    ∀ a : Term 3, Name_d M B (a.eval (rel_env_l M T s t)) := by
  intro a
  cases a with
  | free _ => exact hT
  | bound i => exact Fin.cases ht (Fin.cases hs (fun _ => hT)) i

include O hZF

theorem rel_force_regular_l {T s t} (hT : Name_d M B T) (hs : Name_d M B s) (ht : Name_d M B t) :
    Regular_d M B R z (fun p => Rel_force_d M B R z T p s t) :=
  forces_regular_l O hZF entry_body_m _ (rel_env_name_l hT hs ht)

/-- 被迫相等的两个坐标可同时代入任意名称关系。 -/
theorem rel_force_congr_l {T s t x y p} (hT : Name_d M B T) (hs : Name_d M B s) (ht : Name_d M B t)
    (hx : Name_d M B x) (hy : Name_d M B y) (hp : M.mem p B) (hz : p ≠ z)
    (hsx : Eq_force_d M B R z p s x) (hty : Eq_force_d M B R z p t y) :
    Rel_force_d M B R z T p s t ↔ Rel_force_d M B R z T p x y := by
  apply forces_congr_below_l O hZF entry_body_m (rel_env_l M T s t) (rel_env_l M T x y)
    (rel_env_name_l hT hs ht) (rel_env_name_l hT hx hy) hp ?_ p (below_refl_l O hp hz)
  intro a
  cases a with
  | free _ => exact eq_force_refl_l O hZF hp hT
  | bound i => exact Fin.cases hty (Fin.cases hsx (fun _ => eq_force_refl_l O hZF hp hT)) i

/-- 被迫使的预序公理直接给出每个首阶段条件上的自反性与传递性。 -/
theorem forced_preord_l {A T p} (hA : Name_d M B A) (hT : Name_d M B T)
    (hp : M.mem p B) (hz : p ≠ z)
    (h : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) p) :
    (∀ s, Name_d M B s → Mem_force_d M B R z p s A → Rel_force_d M B R z T p s s) ∧
    ∀ s t v, Name_d M B s → Name_d M B t → Name_d M B v →
      Mem_force_d M B R z p s A → Mem_force_d M B R z p t A → Mem_force_d M B R z p v A →
      Rel_force_d M B R z T p s t → Rel_force_d M B R z T p t v → Rel_force_d M B R z T p s v := by
  have hρ : ∀ a : Term 2, Name_d M B (a.eval (ord_env_l M A T)) := by
    intro a
    cases a with
    | free _ => exact hT
    | bound i => exact Fin.cases hA (fun _ => hT) i
  have push {n} {ρ : Env M n} (hρ : ∀ a : Term n, Name_d M B (a.eval ρ)) {s} (hs : Name_d M B s) :
      ∀ a : Term (n+1), Name_d M B (a.eval (ρ.push s)) := by
    intro a
    cases a with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  have hrefl := (forces_conj_l _ _ _ p).mp h |>.1
  have htrans := (forces_conj_l _ _ _ p).mp h |>.2
  constructor
  · intro s hs hm
    have h := (forces_all_l hZF.1 _ _ p).mp hrefl s hs
    have h := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ (push hρ hs)).1
      (forces_regular_l O hZF _ _ (push hρ hs)) hp hz h
      ((code_mem_l M hZF.1 B R z _ _ _ p).mpr hm)
    exact (force_rel_at_l M hZF.1 ((ord_env_l M A T).push s) p .newest .newest (.bound 2)).mp h
  · intro s t v hs ht hv hsA htA hvA hst htv
    have h := (forces_all_l hZF.1 _ _ p).mp ((forces_all_l hZF.1 _ _ p).mp
      ((forces_all_l hZF.1 _ _ p).mp htrans s hs) t ht) v hv
    have hn := push (push (push hρ hs) ht) hv
    have hf := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ hn).1
      (forces_regular_l O hZF _ _ hn) hp hz h
    apply (force_rel_at_l M hZF.1 ((((ord_env_l M A T).push s).push t).push v) p (.bound 2) .newest (.bound 4)).mp
    apply hf
    simp only [forces_conj_l, force_rel_at_l M hZF.1, forces_mem_l hZF.1]
    change Mem_force_d M B R z p s A ∧ Mem_force_d M B R z p t A ∧ Mem_force_d M B R z p v A ∧ _
    refine ⟨hsA, htA, hvA, ?_, ?_⟩
    · exact hst
    · exact htv

/-- 第二阶段关系的内部力迫与其泛型解释精确对应。 -/
theorem rel_force_truth_l {U : M.Domain → Prop} (hU : Generic_d M B R z U)
    {s t T : M.Domain} {x y D : Name_quot_l M B R z U}
    (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y) (hT : Qval_d M B R z U T D) :
    (∃ p, U p ∧ Rel_force_d M B R z T p s t) ↔ Entry_d (extension_l M hZF B R z U) x y D := by
  have hρ : Env_val_d hZF (rel_env_l M T s t) (rel_env_l (extension_l M hZF B R z U) D x y) := by
    intro a
    cases a with
    | free _ => exact hT
    | bound i => exact Fin.cases ht (Fin.cases hs (fun _ => hT)) i
  exact (forcing_truth_l O hZF hU entry_body_m rel_closed_l _ _ hρ).trans
    (entry_sat_l _ (extension_ext_l O hZF hU) _ _ _ _)

/-- 在任意已接受条件以下取得第二阶段关系的力迫见证。 -/
theorem rel_force_below_l {U : M.Domain → Prop} (hU : Generic_d M B R z U)
    {p s t T : M.Domain} {x y D : Name_quot_l M B R z U} (hp : U p)
    (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y) (hT : Qval_d M B R z U T D)
    (h : Entry_d (extension_l M hZF B R z U) x y D) :
    ∃ q, U q ∧ Below_d M B R z q p ∧ Rel_force_d M B R z T q s t := by
  obtain ⟨r, hr, h⟩ := (rel_force_truth_l O hZF hU hs ht hT).mpr h
  obtain ⟨q, hq, hqp, hqr⟩ := hU.directed p r hp hr
  have hq' := hU.proper q hq
  exact ⟨q, hq, ⟨hq'.1, hq'.2, hqp⟩,
    (rel_force_regular_l O hZF (qval_name_l hT) (qval_name_l hs) (qval_name_l ht)).1 r q
      (hU.proper r hr).1 ⟨hq'.1, hq'.2, hqr⟩ h⟩

end YesMetaZFC.Model.Forcing.Internal
