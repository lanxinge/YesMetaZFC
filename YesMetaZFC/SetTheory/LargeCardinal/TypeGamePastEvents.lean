import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastStep
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTrace

/-! # 完整存档与三阶段历史逐轮对应

对应按内部轮号读取同一原五十四项记录。旧行沿实际偶数图搬运后，再随三次
追加保留；新行使用本次真实回答建立对应。所有轮号均来自对象模型的函数图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_trace_d (ω V q C c e a n h : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d ω V q v ∧ Tg_trace_d ω C c e a n h (v 41) (v 15) (v 11)

-- 前九项是原记录及当前历史参数，随后量化同一记录的五十四个坐标。
def tg_saved_trace0_m : Formula 1 9 := rt_exists_m 54
  (.conj (rt_tuple_m (Fin.cases (.bound 54) (Fin.cases (.bound 55)
    (fun i : Fin 54 => .bound (i.castAdd 9)))) (.bound 56))
    (tg_trace_m (.bound 54) (.bound 57) (.bound 58) (.bound 59) (.bound 60)
      (.bound 61) (.bound 62) (.bound 41) (.bound 15) (.bound 11)))

theorem tg_saved_trace0_closed_l : tg_saved_trace0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl, ?_⟩
  apply tg_trace_closed_l <;> rfl

def tg_saved_trace_m {d} (ω V q C c e a n h : Term d) : Formula 1 d :=
  tg_saved_trace0_m.bind (fun i => [ω, V, q, C, c, e, a, n, h].get i)

@[simp] theorem tg_saved_trace_closed_l {d} (ω V q C c e a n h : Term d)
    (hw : ω.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = [])
    (hC : C.freeSupport = []) (hc : c.freeSupport = []) (he : e.freeSupport = [])
    (ha : a.freeSupport = []) (hn : n.freeSupport = []) (hh : h.freeSupport = []) :
    (tg_saved_trace_m ω V q C c e a n h).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_saved_trace0_closed_l
  exact Fin.cases hw (Fin.cases hV (Fin.cases hq (Fin.cases hC (Fin.cases hc
    (Fin.cases he (Fin.cases ha (Fin.cases hn (Fin.cases hh (fun i => Fin.elim0 i)))))))))

theorem tg_saved_trace0_sat_l (hE : Extensional M) (ρ : Env M 9) :
    Formula.satisfies ρ tg_saved_trace0_m ↔
      Tg_saved_trace_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4)
        (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) := by
  rw [tg_saved_trace0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  rw [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, tg_trace_sat_l]
  have new (i : Fin 54) : (rt_push_d ρ 54 v).bound (i.castAdd 9) = v i := rt_push_new_l ρ v i
  have old (i : Fin 9) : (rt_push_d ρ 54 v).bound (Fin.natAdd 54 i) = ρ.bound i := rt_push_old_l ρ v i
  have tuple : (fun i : Fin 56 =>
      ((Fin.cases (.bound 54) (Fin.cases (.bound 55) (fun j : Fin 54 => .bound (j.castAdd 9))) i : Term 63).eval
        (rt_push_d ρ 54 v))) = Fin.cases (ρ.bound 0) (Fin.cases (ρ.bound 1) v) := by
    funext i
    exact Fin.cases (old 0) (Fin.cases (old 1) new) i
  rw [tuple]
  change (Tg_saved_code_d (ρ.bound 0) (ρ.bound 1) ((rt_push_d ρ 54 v).bound 56) v ∧
    Tg_trace_d ((rt_push_d ρ 54 v).bound 54) ((rt_push_d ρ 54 v).bound 57)
      ((rt_push_d ρ 54 v).bound 58) ((rt_push_d ρ 54 v).bound 59) ((rt_push_d ρ 54 v).bound 60)
      ((rt_push_d ρ 54 v).bound 61) ((rt_push_d ρ 54 v).bound 62)
      ((rt_push_d ρ 54 v).bound 41) ((rt_push_d ρ 54 v).bound 15) ((rt_push_d ρ 54 v).bound 11)) ↔ _
  have e0 : (rt_push_d ρ 54 v).bound 54 = ρ.bound 0 := old 0
  have e2 : (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 := old 2
  have e3 : (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 := old 3
  have e4 : (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 := old 4
  have e5 : (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 := old 5
  have e6 : (rt_push_d ρ 54 v).bound 60 = ρ.bound 6 := old 6
  have e7 : (rt_push_d ρ 54 v).bound 61 = ρ.bound 7 := old 7
  have e8 : (rt_push_d ρ 54 v).bound 62 = ρ.bound 8 := old 8
  have e41 : (rt_push_d ρ 54 v).bound 41 = v 41 := new 41
  have e15 : (rt_push_d ρ 54 v).bound 15 = v 15 := new 15
  have e11 : (rt_push_d ρ 54 v).bound 11 = v 11 := new 11
  rw [e0, e2, e3, e4, e5, e6, e7, e8, e41, e15, e11]

theorem tg_saved_trace_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V q C c e a n h : Term d) :
    Formula.satisfies ρ (tg_saved_trace_m ω V q C c e a n h) ↔
      Tg_saved_trace_d (ω.eval ρ) (V.eval ρ) (q.eval ρ) (C.eval ρ) (c.eval ρ)
        (e.eval ρ) (a.eval ρ) (n.eval ρ) (h.eval ρ) := by
  rw [tg_saved_trace_m, Formula.satisfies_bind, tg_saved_trace0_sat_l hE]
  rfl

def Tg_past_events_d (ω H C c e a h : M.Domain) : Prop := ∀ m i Y R μ K η D L V q,
  Tg_past_at_d H m i Y R μ K η D L V q → Tg_saved_trace_d ω V q C c e a m h

def tg_past_events_m {d} (ω H C c e a h : Term d) : Formula 1 d := set[d] ⟪
  ∀ m i Y R μ K η D L V q, ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, D, L, V, q) →
    ⌜tg_saved_trace_m⌝ₚ(⌜ω⌝ₛ, V, q, ⌜C⌝ₛ, ⌜c⌝ₛ, ⌜e⌝ₛ, ⌜a⌝ₛ, m, ⌜h⌝ₛ)⟫
derive_free_closed tg_past_events_m

theorem tg_past_events_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H C c e a h : Term d) :
    Formula.satisfies ρ (tg_past_events_m ω H C c e a h) ↔
      Tg_past_events_d (ω.eval ρ) (H.eval ρ) (C.eval ρ) (c.eval ρ) (e.eval ρ) (a.eval ρ) (h.eval ρ) := by
  simp only [tg_past_events_m, Tg_past_events_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tg_past_at_sat_l hE, tg_saved_trace_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem tg_past_events_empty_l {ω H C c e a h : M.Domain} (empty : ∀ x, ¬ M.mem x H) :
    Tg_past_events_d ω H C c e a h :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (empty p hp).elim

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 对当前层的三次追加可直接重复使用同一包含性结论。 -/
theorem Tg_past_events_d.mono_l {ω H C : M.Domain} (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (c e a h h' : (rt_model_l C nc).Domain) (events : Tg_past_events_d ω H C c.val e.val a.val h.val)
    (sub : M.MemberSubset h.val h'.val) : Tg_past_events_d ω H C c.val e.val a.val h'.val := by
  intro m i Y R μ K η D L V q row
  obtain ⟨v, code, trace⟩ := events m i Y R μ K η D L V q row
  exact ⟨v, code, trace.mono_l hZF trans nc J c e a h h' sub⟩

/-- 同一真实树边逐轮搬运对应，旧完整模型及其记录均保留原值。 -/
theorem Tg_past_events_d.map_l {ω n H X b C C' c e a h h' Y R S d f j : M.Domain}
    (past : Tg_past_d hZF ω n H X b) (hn : M.mem n ω)
    (hω : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I d X R) (my : Smem_d I f Y S) (map : Smap_d I ω d f X Y j)
    (hwX : M.mem ω X) (hc : M.mem c ω) (he : M.mem e ω) (ha : M.mem a ω)
    (iC : Rd_entry_d C C' j) (ih : Rd_entry_d h h' j) (fixed : Tg_past_fixed_d H j)
    (events : Tg_past_events_d ω H C c e a h) : Tg_past_events_d ω H C' c e a h' := by
  intro m i Z T μ K η D L V q row
  obtain ⟨v, code, trace⟩ := events m i Z T μ K η D L V q row
  have saved := (past.read_l hZF row).1
  obtain ⟨ρ, code', _, _, hτ, _, _, hw⟩ := saved.read_l hZF ⟨⟨ω, saved.context.omega⟩⟩
  have eq := rt_tuple_inj_l code code'
  have eτ : v 15 = (ρ.bound 15).val := congrFun eq 17
  have ew : v 11 = (ρ.bound 11).val := congrFun eq 13
  have hm := row.elim fun r hr => hω.transitive hZF n hn m ((past.sequence.2.2 m).mpr ⟨r, hr.1⟩)
  exact ⟨v, code, trace.map_l hZF hω xt yt mx my map hwX hc he ha hm iC ih
    (fixed m i Z T μ K η D L V q row _ (eτ.symm ▸ hτ))
    (fixed m i Z T μ K η D L V q row _ (ew.symm ▸ hw))⟩

/-- 用本次真实回答追加对应；旧行仍读取搬运并延长后的同一历史。 -/
theorem Tg_past_events_d.push_l {ω n H n' H' X b C c e a h i Y R μ K η D L V q : M.Domain}
    (updated : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η D L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (events : Tg_past_events_d ω H C c e a h) (v : Fin 54 → M.Domain) (code : Tg_saved_code_d ω V q v)
    (trace : Tg_trace_d ω C c e a n h (v 41) (v 15) (v 11)) : Tg_past_events_d ω H' C c e a h := by
  intro m i₀ Y₀ R₀ μ₀ K₀ η₀ D₀ L₀ V₀ q₀ row
  obtain ⟨r, hr, cell⟩ := row
  rcases (succ m).mp ((updated.sequence.2.2 m).mpr ⟨r, hr⟩) with lt | eq
  · exact events m i₀ Y₀ R₀ μ₀ K₀ η₀ D₀ L₀ V₀ q₀ ⟨r, (entries m r lt).mp hr, cell⟩
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, cell'⟩ := newest
    have eq := updated.sequence.2.1.2 n r s hr hs
    subst s
    have eq := rt_tuple_inj_l cell cell'
    have eV : V₀ = V := congrFun eq 8
    have eq' : q₀ = q := congrFun eq 9
    subst V₀ q₀
    exact ⟨v, code, trace⟩

end YesMetaZFC.SetTheory.LargeCardinal
