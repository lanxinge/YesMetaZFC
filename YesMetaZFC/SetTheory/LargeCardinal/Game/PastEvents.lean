import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay

/-! # 完整存档与三阶段历史逐轮对应

旧行保留保存时的模型及五十四项原记录，事件对应则在当前模型中解释。
初等搬运逐项使用实际坐标像；自然数、标签及共同层回答的固定性由树后继构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_saved_trace_d (Y R ω V q B T C c e a n h : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d Y R ω V q v ∧ Tg_trace_d I B T ω C c e a n h (v 41) (v 15) (v 11)

def tg_saved_trace0_m : Formula 1 13 := rt_exists_m 54 (.conj
  (tg_saved_code_m (.bound 54) (.bound 55) (.bound 56) (.bound 57) (.bound 58)
    (fun i : Fin 54 => .bound (i.castAdd 13)))
  (tg_trace_m (.bound 59) (.bound 60) (.bound 56) (.bound 61) (.bound 62) (.bound 63) (.bound 64)
    (.bound 65) (.bound 66) (.bound 41) (.bound 15) (.bound 11)))

theorem tg_saved_trace0_closed_l : tg_saved_trace0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨tg_saved_code_closed_l _ _ _ _ _ _ rfl rfl rfl rfl rfl (fun _ => rfl), ?_⟩
  apply tg_trace_closed_l <;> rfl

theorem tg_saved_trace0_sat_l (ρ : Env M 13) : Formula.satisfies ρ tg_saved_trace0_m ↔
    Tg_saved_trace_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5)
      (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12) := by
  rw [tg_saved_trace0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, tg_saved_code_sat_l, tg_trace_sat_l I, Term.eval_bound]
  have tuple : (fun i : Fin 54 => (rt_push_d ρ 54 v).bound (i.castAdd 13)) = v := funext (rt_push_new_l ρ v)
  rw [tuple]
  rw [
    show (rt_push_d ρ 54 v).bound 54 = ρ.bound 0 from rt_push_old_l ρ v 0,
    show (rt_push_d ρ 54 v).bound 55 = ρ.bound 1 from rt_push_old_l ρ v 1,
    show (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 from rt_push_old_l ρ v 2,
    show (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 from rt_push_old_l ρ v 3,
    show (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 from rt_push_old_l ρ v 4,
    show (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 from rt_push_old_l ρ v 5,
    show (rt_push_d ρ 54 v).bound 60 = ρ.bound 6 from rt_push_old_l ρ v 6,
    show (rt_push_d ρ 54 v).bound 61 = ρ.bound 7 from rt_push_old_l ρ v 7,
    show (rt_push_d ρ 54 v).bound 62 = ρ.bound 8 from rt_push_old_l ρ v 8,
    show (rt_push_d ρ 54 v).bound 63 = ρ.bound 9 from rt_push_old_l ρ v 9,
    show (rt_push_d ρ 54 v).bound 64 = ρ.bound 10 from rt_push_old_l ρ v 10,
    show (rt_push_d ρ 54 v).bound 65 = ρ.bound 11 from rt_push_old_l ρ v 11,
    show (rt_push_d ρ 54 v).bound 66 = ρ.bound 12 from rt_push_old_l ρ v 12]
  rfl

def tg_saved_trace_m {d} (Y R ω V q B T C c e a n h : Term d) : Formula 1 d :=
  tg_saved_trace0_m.bind (fun i => [Y,R,ω,V,q,B,T,C,c,e,a,n,h].get i)

@[simp] theorem tg_saved_trace_closed_l {d} (Y R ω V q B T C c e a n h : Term d)
    (hY : Y.freeSupport = []) (hR : R.freeSupport = []) (hω : ω.freeSupport = []) (hV : V.freeSupport = [])
    (hq : q.freeSupport = []) (hB : B.freeSupport = []) (hT : T.freeSupport = []) (hC : C.freeSupport = [])
    (hc : c.freeSupport = []) (he : e.freeSupport = []) (ha : a.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) : (tg_saved_trace_m Y R ω V q B T C c e a n h).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hY (Fin.cases hR (Fin.cases hω (Fin.cases hV (Fin.cases hq (Fin.cases hB (Fin.cases hT
      (Fin.cases hC (Fin.cases hc (Fin.cases he (Fin.cases ha (Fin.cases hn (Fin.cases hh (fun i => Fin.elim0 i)))))))))))))) _).mpr
        tg_saved_trace0_closed_l

theorem tg_saved_trace_sat_l {d} (ρ : Env M d) (Y R ω V q B T C c e a n h : Term d) :
    Formula.satisfies ρ (tg_saved_trace_m Y R ω V q B T C c e a n h) ↔
      Tg_saved_trace_d I (Y.eval ρ) (R.eval ρ) (ω.eval ρ) (V.eval ρ) (q.eval ρ) (B.eval ρ) (T.eval ρ)
        (C.eval ρ) (c.eval ρ) (e.eval ρ) (a.eval ρ) (n.eval ρ) (h.eval ρ) := by
  rw [tg_saved_trace_m, Formula.satisfies_bind, tg_saved_trace0_sat_l I]
  rfl

def Tg_past_events_d (ω H B T C c e a h : M.Domain) : Prop := ∀ m i Y R μ K η D L V q,
  Tg_past_at_d H m i Y R μ K η D L V q → Tg_saved_trace_d I Y R ω V q B T C c e a m h

def tg_past_events_m {d} (ω H B T C c e a h : Term d) : Formula 1 d := set[d] ⟪
  ∀ m i Y R μ K η D L V q, ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, D, L, V, q) →
    ⌜tg_saved_trace_m⌝ₚ(Y,R,⌜ω⌝ₛ,V,q,⌜B⌝ₛ,⌜T⌝ₛ,⌜C⌝ₛ,⌜c⌝ₛ,⌜e⌝ₛ,⌜a⌝ₛ,m,⌜h⌝ₛ)⟫
derive_free_closed tg_past_events_m

theorem tg_past_events_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H B T C c e a h : Term d) :
    Formula.satisfies ρ (tg_past_events_m ω H B T C c e a h) ↔
      Tg_past_events_d I (ω.eval ρ) (H.eval ρ) (B.eval ρ) (T.eval ρ) (C.eval ρ)
        (c.eval ρ) (e.eval ρ) (a.eval ρ) (h.eval ρ) := by
  simp only [tg_past_events_m, Tg_past_events_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tg_past_at_sat_l hE, tg_saved_trace_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem tg_past_events_empty_l {ω H B T C c e a h : M.Domain} (empty : ∀ x, ¬ M.mem x H) :
    Tg_past_events_d I ω H B T C c e a h :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (empty p hp).elim

/-- 旧历史的逐点包含保持全部存档对应。 -/
theorem Tg_past_events_d.mono_l (hE : Extensional M) {b X R ω H C : M.Domain}
    (model : Smem_d I b X R) (xt : M.TransitiveSet X) (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (c e a h h' : (rt_model_l C nc).Domain) (events : Tg_past_events_d I ω H X R C c.val e.val a.val h.val)
    (sub : M.MemberSubset h.val h'.val) : Tg_past_events_d I ω H X R C c.val e.val a.val h'.val := by
  intro m i Y S μ K η D L V q row
  obtain ⟨v, code, trace⟩ := events m i Y S μ K η D L V q row
  exact ⟨v, code, trace.mono_l I hE model xt trans nc J c e a h h' sub⟩

/-- 每行的实际坐标像使整列对应沿同一原关系图搬运。 -/
theorem Tg_past_events_d.map_l (hZF : M.Models ZF)
    {ω H X R b Y S d j C C' c c' e e' a a' h h' : M.Domain}
    (hw : M.IsOmega ω) (mx : Smdl_d I b X R) (my : Smdl_d I d Y S) (map : Smap_d I ω b d X Y j)
    (iω : M.PairMember I ω ω j) (iC : M.PairMember I C C' j) (ic : M.PairMember I c c' j)
    (ie : M.PairMember I e e' j) (ia : M.PairMember I a a' j) (ih : M.PairMember I h h' j)
    (fixed : ∀ m i U T μ K η D L V q, Tg_past_at_d H m i U T μ K η D L V q → ∀ v,
      Tg_saved_code_d U T ω V q v → Tg_trace_d I X R ω C c e a m h (v 41) (v 15) (v 11) →
        M.PairMember I m m j ∧ M.PairMember I (v 41) (v 41) j ∧
        M.PairMember I (v 15) (v 15) j ∧ M.PairMember I (v 11) (v 11) j)
    (events : Tg_past_events_d I ω H X R C c e a h) : Tg_past_events_d I ω H Y S C' c' e' a' h' := by
  intro m i U T μ K η D L V q row
  obtain ⟨v, code, trace⟩ := events m i U T μ K η D L V q row
  obtain ⟨im,it,iτ,iw⟩ := fixed m i U T μ K η D L V q row v code trace
  exact ⟨v, code, trace.map_l I hZF hw mx my map iω iC ic ie ia im ih it iτ iw⟩

/-- 本次真实回答追加一行，旧行继续使用搬运并延长后的同一历史。 -/
theorem Tg_past_events_d.push_l (hZF : M.Models ZF) {ω n H n' H' X T b C c e a h i Y R μ K η D L V q : M.Domain}
    (updated : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η D L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (events : Tg_past_events_d I ω H X T C c e a h) (v : Fin 54 → M.Domain) (code : Tg_saved_code_d Y R ω V q v)
    (trace : Tg_trace_d I X T ω C c e a n h (v 41) (v 15) (v 11)) : Tg_past_events_d I ω H' X T C c e a h := by
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
    have eY : Y₀ = Y := congrFun eq 1
    have eR : R₀ = R := congrFun eq 2
    have eV : V₀ = V := congrFun eq 8
    have eq' : q₀ = q := congrFun eq 9
    subst Y₀ R₀ V₀ q₀
    exact ⟨v, code, trace⟩

end YesMetaZFC.SetTheory.LargeCardinal
