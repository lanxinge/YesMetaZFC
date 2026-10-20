import YesMetaZFC.SetTheory.LargeCardinal.TypeGameEventHistory
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite

/-! # 旧轮与当前原策略历史的有界对应

对应只携带原自然数标签列、回答的域和类型；辅助域及新类型仍从历史的实际
事件读取。把事件公式限制到当前反射层后，整份对应是背景中的 Δ₀ 公式，
可沿实际偶数嵌入搬运。标签列由有限函数固定性处理，回答由共同秩段固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_event_in0_m : Formula 1 8 := lr_rel_m tg_round_event0_m .newest (fun i => .bound i.succ)

theorem tg_event_in0_closed_l : tg_event_in0_m.FreeClosed :=
  lr_rel_closed_l _ tg_round_event0_closed_l _ _ rfl (fun _ => rfl)

theorem tg_event_in0_delta_l : tg_event_in0_m.IsDelta0 := lr_rel_delta_l ..

-- 十个坐标依次为 ω、反射层、三阶段时钟、零、一、轮号、当前历史、旧标签、旧域、旧类型。
def tg_trace0_m : Formula 1 10 :=
  let v : Fin 10 → Term 10 := Term.bound
  .conj (.mem (v 5) (v 1)) (.conj (.mem (v 7) (v 1))
    (Formula.existsMem (v 0) (Formula.existsMem (v 1).weaken
      (.conj (fn0_m (.bound 1) (.bound 2) (.bound 9))
        (.conj (kpair0_m .newest (.bound 10) (.bound 11))
          (tg_event_in0_m.bind
            (fun i => [.bound 3, .bound 4, .bound 5, .bound 6, .bound 7, .bound 8, .bound 9, .newest].get i)))))))

theorem tg_trace0_closed_l : tg_trace0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_trace0_m, Definitional.Formula.FreeClosed]
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_event_in0_closed_l
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))

theorem tg_trace0_delta_l : tg_trace0_m.IsDelta0 :=
  .conj (.mem ..) (.conj (.mem ..) (.existsMem _ (.existsMem _
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (tg_event_in0_delta_l.bind_l _))))))

def Tg_trace_d (ω C c e a n h t τ w : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [ω, C, c, e, a, n, h, t, τ, w].get i, fun _ => ω⟩ : Env M 10) tg_trace0_m

def tg_trace_m {d} (ω C c e a n h t τ w : Term d) : Formula 1 d :=
  tg_trace0_m.bind (fun i => [ω, C, c, e, a, n, h, t, τ, w].get i)

@[simp] theorem tg_trace_closed_l {d} (ω C c e a n h t τ w : Term d)
    (hw : ω.freeSupport = []) (hC : C.freeSupport = []) (hc : c.freeSupport = [])
    (he : e.freeSupport = []) (ha : a.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) (ht : t.freeSupport = []) (hτ : τ.freeSupport = []) (hw' : w.freeSupport = []) :
    (tg_trace_m ω C c e a n h t τ w).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_trace0_closed_l
  intro i
  exact Fin.cases hw (Fin.cases hC (Fin.cases hc (Fin.cases he (Fin.cases ha
    (Fin.cases hn (Fin.cases hh (Fin.cases ht (Fin.cases hτ (Fin.cases hw' (fun j => Fin.elim0 j)))))))))) i

theorem tg_trace_sat_l {d} (ρ : Env M d) (ω C c e a n h t τ w : Term d) :
    Formula.satisfies ρ (tg_trace_m ω C c e a n h t τ w) ↔
      Tg_trace_d (ω.eval ρ) (C.eval ρ) (c.eval ρ) (e.eval ρ) (a.eval ρ) (n.eval ρ)
        (h.eval ρ) (t.eval ρ) (τ.eval ρ) (w.eval ρ) := by
  rw [tg_trace_m, Formula.satisfies_bind]
  apply Formula.closed_env_l _ tg_trace0_closed_l
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 将实际产生的辅助事件与回答事件写入背景有界对应。 -/
theorem tg_trace_build_l {ω C k τ w : M.Domain} (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C})
    (c e a n h t z : (rt_model_l C nc).Domain) (hk : M.mem k ω) (fn : Fn0_d k ω t.val)
    (pair : KPair_d M z.val τ w) (event : Formula.satisfies
      (⟨fun i => [c, e, a, n, h, t, z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7) tg_round_event0_m) :
    Tg_trace_d ω C c.val e.val a.val n.val h.val t.val τ w := by
  apply (Formula.satisfies_conj_iff ..).mpr
  refine ⟨n.property, (Formula.satisfies_conj_iff ..).mpr ⟨t.property, ?_⟩⟩
  apply (Formula.satisfies_existsMem_iff ..).mpr
  refine ⟨k, hk, (Formula.satisfies_existsMem_iff ..).mpr ⟨z.val, z.property, ?_⟩⟩
  apply (Formula.satisfies_conj_iff ..).mpr
  refine ⟨(fn0_sat_l hZF.1 ..).mpr fn, (Formula.satisfies_conj_iff ..).mpr ⟨(kpair0_sat_l hZF.1 ..).mpr pair, ?_⟩⟩
  have rel := (sc_relative_sat_l trans nc tg_round_event0_m tg_round_event0_closed_l
    (⟨fun i => [c, e, a, n, h, t, z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7)
    ((⟨fun i => [c.val, e.val, a.val, n.val, h.val, t.val, z.val].get i, fun _ => ω⟩ : Env M 7).push C)
    .newest (fun i => .bound i.succ)
    rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))).mpr event
  apply (Formula.satisfies_bind ..).mpr
  apply (Formula.closed_env_l tg_event_in0_m tg_event_in0_closed_l (ρ := _) (η := _) ?_).mp rel
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i

/-- 从背景对应读回当前层中的同一标签及回答，配对等式仍是背景真等式。 -/
theorem Tg_trace_d.read_l {ω C n t τ w : M.Domain} (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (c e a h : (rt_model_l C nc).Domain)
    (trace : Tg_trace_d ω C c.val e.val a.val n h.val t τ w) :
    ∃ k, M.mem k ω ∧ Fn0_d k ω t ∧ ∃ n' t' z : (rt_model_l C nc).Domain,
      n'.val = n ∧ t'.val = t ∧ KPair_d M z.val τ w ∧ Formula.satisfies
        (⟨fun i => [c, e, a, n', h, t', z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7) tg_round_event0_m := by
  obtain ⟨hn, trace⟩ := (Formula.satisfies_conj_iff ..).mp trace
  obtain ⟨ht, trace⟩ := (Formula.satisfies_conj_iff ..).mp trace
  obtain ⟨k, hk, trace⟩ := (Formula.satisfies_existsMem_iff ..).mp trace
  obtain ⟨z, hz, trace⟩ := (Formula.satisfies_existsMem_iff ..).mp trace
  obtain ⟨fn, trace⟩ := (Formula.satisfies_conj_iff ..).mp trace
  obtain ⟨pair, event⟩ := (Formula.satisfies_conj_iff ..).mp trace
  have fn := (fn0_sat_l hZF.1 ..).mp fn
  have pair := (kpair0_sat_l hZF.1 ..).mp pair
  refine ⟨k, hk, fn, ⟨n, hn⟩, ⟨t, ht⟩, ⟨z, hz⟩, rfl, rfl, pair, ?_⟩
  have event := (Formula.satisfies_bind ..).mp event
  have rel : Formula.satisfies
      ((⟨fun i => [c.val, e.val, a.val, n, h.val, t, z].get i, fun _ => ω⟩ : Env M 7).push C) tg_event_in0_m := by
    apply (Formula.closed_env_l tg_event_in0_m tg_event_in0_closed_l (ρ := _) (η := _) ?_).mp event
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i
  exact (sc_relative_sat_l trans nc tg_round_event0_m tg_round_event0_closed_l
    (⟨fun i => [c, e, a, ⟨n, hn⟩, h, ⟨t, ht⟩, ⟨z, hz⟩].get i, fun _ => ⟨z, hz⟩⟩ : Env (rt_model_l C nc) 7)
    ((⟨fun i => [c.val, e.val, a.val, n, h.val, t, z].get i, fun _ => ω⟩ : Env M 7).push C)
    .newest (fun i => .bound i.succ)
    rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))).mp rel

/-- 旧历史逐项包含于新历史时，整份旧轮对应保留。 -/
theorem Tg_trace_d.mono_l {ω C n t τ w : M.Domain} (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (c e a h h' : (rt_model_l C nc).Domain) (trace : Tg_trace_d ω C c.val e.val a.val n h.val t τ w)
    (sub : M.MemberSubset h.val h'.val) : Tg_trace_d ω C c.val e.val a.val n h'.val t τ w := by
  obtain ⟨k, hk, fn, n', t', z, en, et, pair, event⟩ := trace.read_l hZF trans nc c e a h
  have ext := rt_model_ext_l hZF.1 trans nc
  have event := ((tg_round_event_sat_l J ext ..).mp event).mono_l J (fun x hx => sub x.val hx)
  exact en ▸ et ▸ tg_trace_build_l hZF trans nc c e a n' h' t' z hk (et.symm ▸ fn) pair
    ((tg_round_event_sat_l J ext ..).mpr event)

/-- 实际偶数边同时搬运当前历史并保留每一旧轮的标签和回答。 -/
theorem Tg_trace_d.map_l {ω X R b Y S d j C C' c e a n h h' t τ w : M.Domain}
    (hω : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I b X R) (my : Smem_d I d Y S) (map : Smap_d I ω b d X Y j)
    (hwX : M.mem ω X) (hc : M.mem c ω) (he : M.mem e ω) (ha : M.mem a ω) (hn : M.mem n ω)
    (iC : Rd_entry_d C C' j) (ih : Rd_entry_d h h' j)
    (iτ : Rd_entry_d τ τ j) (iw : Rd_entry_d w w j) (trace : Tg_trace_d ω C c e a n h t τ w) :
    Tg_trace_d ω C' c e a n h' t τ w := by
  have facts := (Formula.satisfies_conj_iff ..).mp trace |>.2
  obtain ⟨ht, facts⟩ := (Formula.satisfies_conj_iff ..).mp facts
  obtain ⟨k, hk, facts⟩ := (Formula.satisfies_existsMem_iff ..).mp facts
  obtain ⟨_, _, facts⟩ := (Formula.satisfies_existsMem_iff ..).mp facts
  have fn := (fn0_sat_l hZF.1 ..).mp ((Formula.satisfies_conj_iff ..).mp facts).1
  have natural := map.natural_l hZF hω xt yt mx my hwX
  have it := map.finite_fixed_l hZF hω xt yt mx my hwX hk
    (xt C (map.1.1.input_mem_of_pairMember iC) t ht) fn
  exact (smap_delta_l I hZF hω xt yt mx my map tg_trace0_m tg_trace0_closed_l tg_trace0_delta_l
    (⟨fun i => [ω, C, c, e, a, n, h, t, τ, w].get i, fun _ => ω⟩ : Env M 10)
    (⟨fun i => [ω, C', c, e, a, n, h', t, τ, w].get i, fun _ => ω⟩ : Env M 10)
    (Fin.cases (map.omega_l I hZF hω xt yt mx my hwX) (Fin.cases iC (Fin.cases (natural c hc)
      (Fin.cases (natural e he) (Fin.cases (natural a ha) (Fin.cases (natural n hn)
      (Fin.cases ih (Fin.cases it (Fin.cases iτ (Fin.cases iw (fun i => Fin.elim0 i)))))))))))).mp trace

end YesMetaZFC.SetTheory.LargeCardinal
